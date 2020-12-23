%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:13 EST 2020

% Result     : Theorem 23.25s
% Output     : CNFRefutation 23.25s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 296 expanded)
%              Number of leaves         :   45 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 711 expanded)
%              Number of equality atoms :   55 ( 213 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_122,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_1'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_216,plain,(
    ! [C_100,A_101,B_102] :
      ( r2_hidden(C_100,A_101)
      | ~ r2_hidden(C_100,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_241,plain,(
    ! [A_106,A_107] :
      ( r2_hidden('#skF_1'(A_106),A_107)
      | ~ m1_subset_1(A_106,k1_zfmisc_1(A_107))
      | k1_xboole_0 = A_106 ) ),
    inference(resolution,[status(thm)],[c_52,c_216])).

tff(c_48,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_mcart_1(A_33) = B_34
      | ~ r2_hidden(A_33,k2_zfmisc_1(k1_tarski(B_34),C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_521,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_mcart_1('#skF_1'(A_137)) = B_138
      | ~ m1_subset_1(A_137,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_138),C_139)))
      | k1_xboole_0 = A_137 ) ),
    inference(resolution,[status(thm)],[c_241,c_48])).

tff(c_532,plain,
    ( k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_521])).

tff(c_535,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_532])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_137,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,B_76)
      | k4_xboole_0(k1_tarski(A_75),B_76) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_153,plain,(
    ! [A_78] :
      ( r2_hidden(A_78,k1_xboole_0)
      | k1_tarski(A_78) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_137])).

tff(c_38,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_159,plain,(
    ! [A_78] :
      ( ~ r1_tarski(k1_xboole_0,A_78)
      | k1_tarski(A_78) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_38])).

tff(c_163,plain,(
    ! [A_78] : k1_tarski(A_78) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_159])).

tff(c_554,plain,(
    ! [A_78] : k1_tarski(A_78) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_163])).

tff(c_566,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_58])).

tff(c_120,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(k1_tarski(A_73),B_74) = k1_xboole_0
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_73] :
      ( k1_tarski(A_73) = k1_xboole_0
      | ~ r2_hidden(A_73,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_6])).

tff(c_164,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_127])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_182,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_173])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_84,plain,(
    ! [A_65] :
      ( v1_funct_1(A_65)
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_88,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_84])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_220,plain,(
    ! [A_103,B_104] :
      ( k1_funct_1(A_103,B_104) = k1_xboole_0
      | r2_hidden(B_104,k1_relat_1(A_103))
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_228,plain,(
    ! [B_104] :
      ( k1_funct_1(k1_xboole_0,B_104) = k1_xboole_0
      | r2_hidden(B_104,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_220])).

tff(c_232,plain,(
    ! [B_104] :
      ( k1_funct_1(k1_xboole_0,B_104) = k1_xboole_0
      | r2_hidden(B_104,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_88,c_228])).

tff(c_233,plain,(
    ! [B_104] : k1_funct_1(k1_xboole_0,B_104) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_232])).

tff(c_550,plain,(
    ! [B_104] : k1_funct_1('#skF_4',B_104) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_535,c_233])).

tff(c_601,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_56])).

tff(c_560,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_20])).

tff(c_662,plain,(
    ! [A_153] :
      ( r2_hidden('#skF_1'(A_153),A_153)
      | A_153 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_52])).

tff(c_54,plain,(
    ! [D_61,C_60,B_59,A_58] :
      ( r2_hidden(k1_funct_1(D_61,C_60),B_59)
      | k1_xboole_0 = B_59
      | ~ r2_hidden(C_60,A_58)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(D_61,A_58,B_59)
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_573,plain,(
    ! [D_61,C_60,B_59,A_58] :
      ( r2_hidden(k1_funct_1(D_61,C_60),B_59)
      | B_59 = '#skF_4'
      | ~ r2_hidden(C_60,A_58)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(D_61,A_58,B_59)
      | ~ v1_funct_1(D_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_54])).

tff(c_44279,plain,(
    ! [D_893,A_894,B_895] :
      ( r2_hidden(k1_funct_1(D_893,'#skF_1'(A_894)),B_895)
      | B_895 = '#skF_4'
      | ~ m1_subset_1(D_893,k1_zfmisc_1(k2_zfmisc_1(A_894,B_895)))
      | ~ v1_funct_2(D_893,A_894,B_895)
      | ~ v1_funct_1(D_893)
      | A_894 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_662,c_573])).

tff(c_44347,plain,(
    ! [B_895,A_894] :
      ( r2_hidden('#skF_4',B_895)
      | B_895 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_894,B_895)))
      | ~ v1_funct_2('#skF_4',A_894,B_895)
      | ~ v1_funct_1('#skF_4')
      | A_894 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_44279])).

tff(c_44819,plain,(
    ! [B_900,A_901] :
      ( r2_hidden('#skF_4',B_900)
      | B_900 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_901,B_900)
      | A_901 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_560,c_44347])).

tff(c_44822,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_44819])).

tff(c_44826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_554,c_566,c_601,c_44822])).

tff(c_44828,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_44827,plain,(
    k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_44,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden(k1_mcart_1(A_30),B_31)
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44833,plain,(
    ! [A_902,B_903,C_904] :
      ( r2_hidden(k1_mcart_1('#skF_1'(A_902)),B_903)
      | ~ m1_subset_1(A_902,k1_zfmisc_1(k2_zfmisc_1(B_903,C_904)))
      | k1_xboole_0 = A_902 ) ),
    inference(resolution,[status(thm)],[c_241,c_44])).

tff(c_44839,plain,
    ( r2_hidden(k1_mcart_1('#skF_1'('#skF_4')),k1_tarski('#skF_2'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_44833])).

tff(c_44845,plain,
    ( r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44827,c_44839])).

tff(c_44846,plain,(
    r2_hidden('#skF_2',k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44828,c_44845])).

tff(c_44856,plain,(
    ! [D_905,C_906,B_907,A_908] :
      ( r2_hidden(k1_funct_1(D_905,C_906),B_907)
      | k1_xboole_0 = B_907
      | ~ r2_hidden(C_906,A_908)
      | ~ m1_subset_1(D_905,k1_zfmisc_1(k2_zfmisc_1(A_908,B_907)))
      | ~ v1_funct_2(D_905,A_908,B_907)
      | ~ v1_funct_1(D_905) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_84146,plain,(
    ! [D_9551,B_9552] :
      ( r2_hidden(k1_funct_1(D_9551,'#skF_2'),B_9552)
      | k1_xboole_0 = B_9552
      | ~ m1_subset_1(D_9551,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_9552)))
      | ~ v1_funct_2(D_9551,k1_tarski('#skF_2'),B_9552)
      | ~ v1_funct_1(D_9551) ) ),
    inference(resolution,[status(thm)],[c_44846,c_44856])).

tff(c_84245,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_84146])).

tff(c_84256,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_84245])).

tff(c_84258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_84256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n005.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 20:13:17 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.25/12.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.25/12.94  
% 23.25/12.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.25/12.95  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 23.25/12.95  
% 23.25/12.95  %Foreground sorts:
% 23.25/12.95  
% 23.25/12.95  
% 23.25/12.95  %Background operators:
% 23.25/12.95  
% 23.25/12.95  
% 23.25/12.95  %Foreground operators:
% 23.25/12.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.25/12.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.25/12.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.25/12.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 23.25/12.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.25/12.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 23.25/12.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.25/12.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.25/12.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.25/12.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.25/12.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.25/12.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.25/12.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.25/12.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.25/12.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 23.25/12.95  tff('#skF_2', type, '#skF_2': $i).
% 23.25/12.95  tff('#skF_3', type, '#skF_3': $i).
% 23.25/12.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.25/12.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 23.25/12.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.25/12.95  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 23.25/12.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.25/12.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.25/12.95  tff('#skF_4', type, '#skF_4': $i).
% 23.25/12.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.25/12.95  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 23.25/12.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.25/12.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.25/12.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.25/12.95  
% 23.25/12.96  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 23.25/12.96  tff(f_122, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 23.25/12.96  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 23.25/12.96  tff(f_101, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 23.25/12.96  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.25/12.96  tff(f_30, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 23.25/12.96  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 23.25/12.96  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 23.25/12.96  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 23.25/12.96  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.25/12.96  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.25/12.96  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 23.25/12.96  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 23.25/12.96  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 23.25/12.96  tff(f_134, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 23.25/12.96  tff(f_95, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 23.25/12.96  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.25/12.96  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.25/12.96  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.25/12.96  tff(c_62, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.25/12.96  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.25/12.96  tff(c_52, plain, (![A_36]: (r2_hidden('#skF_1'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.25/12.96  tff(c_216, plain, (![C_100, A_101, B_102]: (r2_hidden(C_100, A_101) | ~r2_hidden(C_100, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.25/12.96  tff(c_241, plain, (![A_106, A_107]: (r2_hidden('#skF_1'(A_106), A_107) | ~m1_subset_1(A_106, k1_zfmisc_1(A_107)) | k1_xboole_0=A_106)), inference(resolution, [status(thm)], [c_52, c_216])).
% 23.25/12.96  tff(c_48, plain, (![A_33, B_34, C_35]: (k1_mcart_1(A_33)=B_34 | ~r2_hidden(A_33, k2_zfmisc_1(k1_tarski(B_34), C_35)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 23.25/12.96  tff(c_521, plain, (![A_137, B_138, C_139]: (k1_mcart_1('#skF_1'(A_137))=B_138 | ~m1_subset_1(A_137, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_138), C_139))) | k1_xboole_0=A_137)), inference(resolution, [status(thm)], [c_241, c_48])).
% 23.25/12.96  tff(c_532, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_521])).
% 23.25/12.96  tff(c_535, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_532])).
% 23.25/12.96  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 23.25/12.96  tff(c_6, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 23.25/12.96  tff(c_137, plain, (![A_75, B_76]: (r2_hidden(A_75, B_76) | k4_xboole_0(k1_tarski(A_75), B_76)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.25/12.96  tff(c_153, plain, (![A_78]: (r2_hidden(A_78, k1_xboole_0) | k1_tarski(A_78)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_137])).
% 23.25/12.96  tff(c_38, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.25/12.96  tff(c_159, plain, (![A_78]: (~r1_tarski(k1_xboole_0, A_78) | k1_tarski(A_78)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_38])).
% 23.25/12.96  tff(c_163, plain, (![A_78]: (k1_tarski(A_78)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_159])).
% 23.25/12.96  tff(c_554, plain, (![A_78]: (k1_tarski(A_78)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_535, c_163])).
% 23.25/12.96  tff(c_566, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_58])).
% 23.25/12.96  tff(c_120, plain, (![A_73, B_74]: (k4_xboole_0(k1_tarski(A_73), B_74)=k1_xboole_0 | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.25/12.96  tff(c_127, plain, (![A_73]: (k1_tarski(A_73)=k1_xboole_0 | ~r2_hidden(A_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_6])).
% 23.25/12.96  tff(c_164, plain, (![A_73]: (~r2_hidden(A_73, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_163, c_127])).
% 23.25/12.96  tff(c_20, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 23.25/12.96  tff(c_173, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.25/12.96  tff(c_182, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_173])).
% 23.25/12.96  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 23.25/12.96  tff(c_84, plain, (![A_65]: (v1_funct_1(A_65) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_62])).
% 23.25/12.96  tff(c_88, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_84])).
% 23.25/12.96  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 23.25/12.96  tff(c_220, plain, (![A_103, B_104]: (k1_funct_1(A_103, B_104)=k1_xboole_0 | r2_hidden(B_104, k1_relat_1(A_103)) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_80])).
% 23.25/12.96  tff(c_228, plain, (![B_104]: (k1_funct_1(k1_xboole_0, B_104)=k1_xboole_0 | r2_hidden(B_104, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_220])).
% 23.25/12.96  tff(c_232, plain, (![B_104]: (k1_funct_1(k1_xboole_0, B_104)=k1_xboole_0 | r2_hidden(B_104, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_88, c_228])).
% 23.25/12.96  tff(c_233, plain, (![B_104]: (k1_funct_1(k1_xboole_0, B_104)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_164, c_232])).
% 23.25/12.96  tff(c_550, plain, (![B_104]: (k1_funct_1('#skF_4', B_104)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_535, c_535, c_233])).
% 23.25/12.96  tff(c_601, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_56])).
% 23.25/12.96  tff(c_560, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_20])).
% 23.25/12.96  tff(c_662, plain, (![A_153]: (r2_hidden('#skF_1'(A_153), A_153) | A_153='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_535, c_52])).
% 23.25/12.96  tff(c_54, plain, (![D_61, C_60, B_59, A_58]: (r2_hidden(k1_funct_1(D_61, C_60), B_59) | k1_xboole_0=B_59 | ~r2_hidden(C_60, A_58) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(D_61, A_58, B_59) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_134])).
% 23.25/12.96  tff(c_573, plain, (![D_61, C_60, B_59, A_58]: (r2_hidden(k1_funct_1(D_61, C_60), B_59) | B_59='#skF_4' | ~r2_hidden(C_60, A_58) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(D_61, A_58, B_59) | ~v1_funct_1(D_61))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_54])).
% 23.25/12.96  tff(c_44279, plain, (![D_893, A_894, B_895]: (r2_hidden(k1_funct_1(D_893, '#skF_1'(A_894)), B_895) | B_895='#skF_4' | ~m1_subset_1(D_893, k1_zfmisc_1(k2_zfmisc_1(A_894, B_895))) | ~v1_funct_2(D_893, A_894, B_895) | ~v1_funct_1(D_893) | A_894='#skF_4')), inference(resolution, [status(thm)], [c_662, c_573])).
% 23.25/12.96  tff(c_44347, plain, (![B_895, A_894]: (r2_hidden('#skF_4', B_895) | B_895='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_894, B_895))) | ~v1_funct_2('#skF_4', A_894, B_895) | ~v1_funct_1('#skF_4') | A_894='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_44279])).
% 23.25/12.96  tff(c_44819, plain, (![B_900, A_901]: (r2_hidden('#skF_4', B_900) | B_900='#skF_4' | ~v1_funct_2('#skF_4', A_901, B_900) | A_901='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_560, c_44347])).
% 23.25/12.96  tff(c_44822, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_62, c_44819])).
% 23.25/12.96  tff(c_44826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_554, c_566, c_601, c_44822])).
% 23.25/12.96  tff(c_44828, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_532])).
% 23.25/12.96  tff(c_44827, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_532])).
% 23.25/12.96  tff(c_44, plain, (![A_30, B_31, C_32]: (r2_hidden(k1_mcart_1(A_30), B_31) | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 23.25/12.96  tff(c_44833, plain, (![A_902, B_903, C_904]: (r2_hidden(k1_mcart_1('#skF_1'(A_902)), B_903) | ~m1_subset_1(A_902, k1_zfmisc_1(k2_zfmisc_1(B_903, C_904))) | k1_xboole_0=A_902)), inference(resolution, [status(thm)], [c_241, c_44])).
% 23.25/12.96  tff(c_44839, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_4')), k1_tarski('#skF_2')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_44833])).
% 23.25/12.96  tff(c_44845, plain, (r2_hidden('#skF_2', k1_tarski('#skF_2')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44827, c_44839])).
% 23.25/12.96  tff(c_44846, plain, (r2_hidden('#skF_2', k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44828, c_44845])).
% 23.25/12.96  tff(c_44856, plain, (![D_905, C_906, B_907, A_908]: (r2_hidden(k1_funct_1(D_905, C_906), B_907) | k1_xboole_0=B_907 | ~r2_hidden(C_906, A_908) | ~m1_subset_1(D_905, k1_zfmisc_1(k2_zfmisc_1(A_908, B_907))) | ~v1_funct_2(D_905, A_908, B_907) | ~v1_funct_1(D_905))), inference(cnfTransformation, [status(thm)], [f_134])).
% 23.25/12.96  tff(c_84146, plain, (![D_9551, B_9552]: (r2_hidden(k1_funct_1(D_9551, '#skF_2'), B_9552) | k1_xboole_0=B_9552 | ~m1_subset_1(D_9551, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_9552))) | ~v1_funct_2(D_9551, k1_tarski('#skF_2'), B_9552) | ~v1_funct_1(D_9551))), inference(resolution, [status(thm)], [c_44846, c_44856])).
% 23.25/12.96  tff(c_84245, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_84146])).
% 23.25/12.96  tff(c_84256, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_84245])).
% 23.25/12.96  tff(c_84258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_84256])).
% 23.25/12.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.25/12.96  
% 23.25/12.96  Inference rules
% 23.25/12.96  ----------------------
% 23.25/12.96  #Ref     : 0
% 23.25/12.96  #Sup     : 20681
% 23.25/12.96  #Fact    : 24
% 23.25/12.96  #Define  : 0
% 23.25/12.96  #Split   : 14
% 23.25/12.96  #Chain   : 0
% 23.25/12.96  #Close   : 0
% 23.25/12.96  
% 23.25/12.96  Ordering : KBO
% 23.25/12.96  
% 23.25/12.96  Simplification rules
% 23.25/12.96  ----------------------
% 23.25/12.96  #Subsume      : 6825
% 23.25/12.96  #Demod        : 15132
% 23.25/12.96  #Tautology    : 7016
% 23.25/12.96  #SimpNegUnit  : 135
% 23.25/12.96  #BackRed      : 35
% 23.25/12.96  
% 23.25/12.96  #Partial instantiations: 5760
% 23.25/12.96  #Strategies tried      : 1
% 23.25/12.96  
% 23.25/12.96  Timing (in seconds)
% 23.25/12.96  ----------------------
% 23.25/12.96  Preprocessing        : 0.42
% 23.25/12.96  Parsing              : 0.23
% 23.25/12.96  CNF conversion       : 0.03
% 23.25/12.96  Main loop            : 11.79
% 23.25/12.96  Inferencing          : 2.32
% 23.25/12.97  Reduction            : 3.39
% 23.25/12.97  Demodulation         : 2.35
% 23.25/12.97  BG Simplification    : 0.23
% 23.25/12.97  Subsumption          : 5.42
% 23.25/12.97  Abstraction          : 0.41
% 23.25/12.97  MUC search           : 0.00
% 23.25/12.97  Cooper               : 0.00
% 23.25/12.97  Total                : 12.25
% 23.25/12.97  Index Insertion      : 0.00
% 23.25/12.97  Index Deletion       : 0.00
% 23.25/12.97  Index Matching       : 0.00
% 23.25/12.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
