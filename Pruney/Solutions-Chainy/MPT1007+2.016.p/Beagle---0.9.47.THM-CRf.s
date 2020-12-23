%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:13 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 265 expanded)
%              Number of leaves         :   45 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 ( 661 expanded)
%              Number of equality atoms :   52 ( 189 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_121,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_1'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_159,plain,(
    ! [C_91,A_92,B_93] :
      ( r2_hidden(C_91,A_92)
      | ~ r2_hidden(C_91,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_177,plain,(
    ! [A_100,A_101] :
      ( r2_hidden('#skF_1'(A_100),A_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(A_101))
      | k1_xboole_0 = A_100 ) ),
    inference(resolution,[status(thm)],[c_50,c_159])).

tff(c_46,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_mcart_1(A_33) = B_34
      | ~ r2_hidden(A_33,k2_zfmisc_1(k1_tarski(B_34),C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_613,plain,(
    ! [A_148,B_149,C_150] :
      ( k1_mcart_1('#skF_1'(A_148)) = B_149
      | ~ m1_subset_1(A_148,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_149),C_150)))
      | k1_xboole_0 = A_148 ) ),
    inference(resolution,[status(thm)],[c_177,c_46])).

tff(c_624,plain,
    ( k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_613])).

tff(c_627,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_96,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_67] : k1_tarski(A_67) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_96])).

tff(c_662,plain,(
    ! [A_67] : k1_tarski(A_67) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_100])).

tff(c_671,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_56])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_124,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_133,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_124])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_82,plain,(
    ! [A_65] :
      ( v1_funct_1(A_65)
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_230,plain,(
    ! [A_107,B_108] :
      ( k1_funct_1(A_107,B_108) = k1_xboole_0
      | r2_hidden(B_108,k1_relat_1(A_107))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_238,plain,(
    ! [B_108] :
      ( k1_funct_1(k1_xboole_0,B_108) = k1_xboole_0
      | r2_hidden(B_108,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_230])).

tff(c_250,plain,(
    ! [B_110] :
      ( k1_funct_1(k1_xboole_0,B_110) = k1_xboole_0
      | r2_hidden(B_110,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_86,c_238])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_257,plain,(
    ! [B_110] :
      ( ~ r1_tarski(k1_xboole_0,B_110)
      | k1_funct_1(k1_xboole_0,B_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_250,c_36])).

tff(c_264,plain,(
    ! [B_110] : k1_funct_1(k1_xboole_0,B_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_257])).

tff(c_654,plain,(
    ! [B_110] : k1_funct_1('#skF_4',B_110) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_627,c_264])).

tff(c_734,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_54])).

tff(c_665,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_18])).

tff(c_470,plain,(
    ! [D_133,C_134,B_135,A_136] :
      ( r2_hidden(k1_funct_1(D_133,C_134),B_135)
      | k1_xboole_0 = B_135
      | ~ r2_hidden(C_134,A_136)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135)))
      | ~ v1_funct_2(D_133,A_136,B_135)
      | ~ v1_funct_1(D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_485,plain,(
    ! [D_133,A_36,B_135] :
      ( r2_hidden(k1_funct_1(D_133,'#skF_1'(A_36)),B_135)
      | k1_xboole_0 = B_135
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_36,B_135)))
      | ~ v1_funct_2(D_133,A_36,B_135)
      | ~ v1_funct_1(D_133)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_50,c_470])).

tff(c_949,plain,(
    ! [D_179,A_180,B_181] :
      ( r2_hidden(k1_funct_1(D_179,'#skF_1'(A_180)),B_181)
      | B_181 = '#skF_4'
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2(D_179,A_180,B_181)
      | ~ v1_funct_1(D_179)
      | A_180 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_627,c_485])).

tff(c_972,plain,(
    ! [B_181,A_180] :
      ( r2_hidden('#skF_4',B_181)
      | B_181 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2('#skF_4',A_180,B_181)
      | ~ v1_funct_1('#skF_4')
      | A_180 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_949])).

tff(c_1053,plain,(
    ! [B_188,A_189] :
      ( r2_hidden('#skF_4',B_188)
      | B_188 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_189,B_188)
      | A_189 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_665,c_972])).

tff(c_1056,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_1053])).

tff(c_1060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_662,c_671,c_734,c_1056])).

tff(c_1062,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_1061,plain,(
    k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_42,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden(k1_mcart_1(A_30),B_31)
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1166,plain,(
    ! [A_206,B_207,C_208] :
      ( r2_hidden(k1_mcart_1('#skF_1'(A_206)),B_207)
      | ~ m1_subset_1(A_206,k1_zfmisc_1(k2_zfmisc_1(B_207,C_208)))
      | k1_xboole_0 = A_206 ) ),
    inference(resolution,[status(thm)],[c_177,c_42])).

tff(c_1172,plain,
    ( r2_hidden(k1_mcart_1('#skF_1'('#skF_4')),k1_tarski('#skF_2'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_1166])).

tff(c_1178,plain,
    ( r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1172])).

tff(c_1179,plain,(
    r2_hidden('#skF_2',k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1062,c_1178])).

tff(c_52,plain,(
    ! [D_61,C_60,B_59,A_58] :
      ( r2_hidden(k1_funct_1(D_61,C_60),B_59)
      | k1_xboole_0 = B_59
      | ~ r2_hidden(C_60,A_58)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(D_61,A_58,B_59)
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1533,plain,(
    ! [D_239,B_240] :
      ( r2_hidden(k1_funct_1(D_239,'#skF_2'),B_240)
      | k1_xboole_0 = B_240
      | ~ m1_subset_1(D_239,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_240)))
      | ~ v1_funct_2(D_239,k1_tarski('#skF_2'),B_240)
      | ~ v1_funct_1(D_239) ) ),
    inference(resolution,[status(thm)],[c_1179,c_52])).

tff(c_1544,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1533])).

tff(c_1554,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1544])).

tff(c_1556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_1554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.83  
% 3.53/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.84  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.53/1.84  
% 3.53/1.84  %Foreground sorts:
% 3.53/1.84  
% 3.53/1.84  
% 3.53/1.84  %Background operators:
% 3.53/1.84  
% 3.53/1.84  
% 3.53/1.84  %Foreground operators:
% 3.53/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.53/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.53/1.84  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.84  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.53/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.84  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.53/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.84  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.84  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.53/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.84  
% 3.53/1.85  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.53/1.85  tff(f_121, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.53/1.85  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.53/1.85  tff(f_100, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 3.53/1.85  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.53/1.85  tff(f_39, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.53/1.85  tff(f_30, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.53/1.85  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.53/1.85  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.53/1.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.53/1.85  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 3.53/1.85  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.53/1.85  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.53/1.85  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.53/1.85  tff(f_133, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.53/1.85  tff(f_94, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.53/1.85  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.85  tff(c_54, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.85  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.85  tff(c_60, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.85  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.85  tff(c_50, plain, (![A_36]: (r2_hidden('#skF_1'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.53/1.85  tff(c_159, plain, (![C_91, A_92, B_93]: (r2_hidden(C_91, A_92) | ~r2_hidden(C_91, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.53/1.85  tff(c_177, plain, (![A_100, A_101]: (r2_hidden('#skF_1'(A_100), A_101) | ~m1_subset_1(A_100, k1_zfmisc_1(A_101)) | k1_xboole_0=A_100)), inference(resolution, [status(thm)], [c_50, c_159])).
% 3.53/1.85  tff(c_46, plain, (![A_33, B_34, C_35]: (k1_mcart_1(A_33)=B_34 | ~r2_hidden(A_33, k2_zfmisc_1(k1_tarski(B_34), C_35)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.53/1.85  tff(c_613, plain, (![A_148, B_149, C_150]: (k1_mcart_1('#skF_1'(A_148))=B_149 | ~m1_subset_1(A_148, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_149), C_150))) | k1_xboole_0=A_148)), inference(resolution, [status(thm)], [c_177, c_46])).
% 3.53/1.85  tff(c_624, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_613])).
% 3.53/1.85  tff(c_627, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_624])).
% 3.53/1.85  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.53/1.85  tff(c_96, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.85  tff(c_100, plain, (![A_67]: (k1_tarski(A_67)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_96])).
% 3.53/1.85  tff(c_662, plain, (![A_67]: (k1_tarski(A_67)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_100])).
% 3.53/1.85  tff(c_671, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_627, c_56])).
% 3.53/1.85  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.53/1.85  tff(c_18, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.53/1.85  tff(c_124, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.53/1.85  tff(c_133, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_124])).
% 3.53/1.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.53/1.85  tff(c_82, plain, (![A_65]: (v1_funct_1(A_65) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.53/1.85  tff(c_86, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 3.53/1.85  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.53/1.85  tff(c_230, plain, (![A_107, B_108]: (k1_funct_1(A_107, B_108)=k1_xboole_0 | r2_hidden(B_108, k1_relat_1(A_107)) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.85  tff(c_238, plain, (![B_108]: (k1_funct_1(k1_xboole_0, B_108)=k1_xboole_0 | r2_hidden(B_108, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_230])).
% 3.53/1.85  tff(c_250, plain, (![B_110]: (k1_funct_1(k1_xboole_0, B_110)=k1_xboole_0 | r2_hidden(B_110, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_86, c_238])).
% 3.53/1.85  tff(c_36, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.85  tff(c_257, plain, (![B_110]: (~r1_tarski(k1_xboole_0, B_110) | k1_funct_1(k1_xboole_0, B_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_250, c_36])).
% 3.53/1.85  tff(c_264, plain, (![B_110]: (k1_funct_1(k1_xboole_0, B_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_257])).
% 3.53/1.85  tff(c_654, plain, (![B_110]: (k1_funct_1('#skF_4', B_110)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_627, c_264])).
% 3.53/1.85  tff(c_734, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_54])).
% 3.53/1.85  tff(c_665, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_18])).
% 3.53/1.85  tff(c_470, plain, (![D_133, C_134, B_135, A_136]: (r2_hidden(k1_funct_1(D_133, C_134), B_135) | k1_xboole_0=B_135 | ~r2_hidden(C_134, A_136) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))) | ~v1_funct_2(D_133, A_136, B_135) | ~v1_funct_1(D_133))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.53/1.85  tff(c_485, plain, (![D_133, A_36, B_135]: (r2_hidden(k1_funct_1(D_133, '#skF_1'(A_36)), B_135) | k1_xboole_0=B_135 | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_36, B_135))) | ~v1_funct_2(D_133, A_36, B_135) | ~v1_funct_1(D_133) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_50, c_470])).
% 3.53/1.85  tff(c_949, plain, (![D_179, A_180, B_181]: (r2_hidden(k1_funct_1(D_179, '#skF_1'(A_180)), B_181) | B_181='#skF_4' | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2(D_179, A_180, B_181) | ~v1_funct_1(D_179) | A_180='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_627, c_485])).
% 3.53/1.85  tff(c_972, plain, (![B_181, A_180]: (r2_hidden('#skF_4', B_181) | B_181='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2('#skF_4', A_180, B_181) | ~v1_funct_1('#skF_4') | A_180='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_654, c_949])).
% 3.53/1.85  tff(c_1053, plain, (![B_188, A_189]: (r2_hidden('#skF_4', B_188) | B_188='#skF_4' | ~v1_funct_2('#skF_4', A_189, B_188) | A_189='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_665, c_972])).
% 3.53/1.85  tff(c_1056, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_1053])).
% 3.53/1.85  tff(c_1060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_662, c_671, c_734, c_1056])).
% 3.53/1.85  tff(c_1062, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_624])).
% 3.53/1.85  tff(c_1061, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_624])).
% 3.53/1.85  tff(c_42, plain, (![A_30, B_31, C_32]: (r2_hidden(k1_mcart_1(A_30), B_31) | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.53/1.85  tff(c_1166, plain, (![A_206, B_207, C_208]: (r2_hidden(k1_mcart_1('#skF_1'(A_206)), B_207) | ~m1_subset_1(A_206, k1_zfmisc_1(k2_zfmisc_1(B_207, C_208))) | k1_xboole_0=A_206)), inference(resolution, [status(thm)], [c_177, c_42])).
% 3.53/1.85  tff(c_1172, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_4')), k1_tarski('#skF_2')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_1166])).
% 3.53/1.85  tff(c_1178, plain, (r2_hidden('#skF_2', k1_tarski('#skF_2')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1172])).
% 3.53/1.85  tff(c_1179, plain, (r2_hidden('#skF_2', k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1062, c_1178])).
% 3.53/1.85  tff(c_52, plain, (![D_61, C_60, B_59, A_58]: (r2_hidden(k1_funct_1(D_61, C_60), B_59) | k1_xboole_0=B_59 | ~r2_hidden(C_60, A_58) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(D_61, A_58, B_59) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.53/1.85  tff(c_1533, plain, (![D_239, B_240]: (r2_hidden(k1_funct_1(D_239, '#skF_2'), B_240) | k1_xboole_0=B_240 | ~m1_subset_1(D_239, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_240))) | ~v1_funct_2(D_239, k1_tarski('#skF_2'), B_240) | ~v1_funct_1(D_239))), inference(resolution, [status(thm)], [c_1179, c_52])).
% 3.53/1.85  tff(c_1544, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1533])).
% 3.53/1.85  tff(c_1554, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1544])).
% 3.53/1.85  tff(c_1556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_1554])).
% 3.53/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.85  
% 3.53/1.85  Inference rules
% 3.53/1.85  ----------------------
% 3.53/1.85  #Ref     : 0
% 3.53/1.85  #Sup     : 318
% 3.53/1.85  #Fact    : 2
% 3.53/1.85  #Define  : 0
% 3.53/1.85  #Split   : 2
% 3.53/1.85  #Chain   : 0
% 3.53/1.85  #Close   : 0
% 3.53/1.85  
% 3.53/1.85  Ordering : KBO
% 3.53/1.85  
% 3.53/1.85  Simplification rules
% 3.53/1.85  ----------------------
% 3.53/1.85  #Subsume      : 83
% 3.53/1.85  #Demod        : 179
% 3.53/1.85  #Tautology    : 100
% 3.53/1.85  #SimpNegUnit  : 19
% 3.53/1.85  #BackRed      : 32
% 3.53/1.85  
% 3.53/1.85  #Partial instantiations: 0
% 3.53/1.85  #Strategies tried      : 1
% 3.53/1.85  
% 3.53/1.85  Timing (in seconds)
% 3.53/1.85  ----------------------
% 3.53/1.85  Preprocessing        : 0.44
% 3.53/1.85  Parsing              : 0.27
% 3.53/1.85  CNF conversion       : 0.02
% 3.53/1.85  Main loop            : 0.50
% 3.53/1.85  Inferencing          : 0.18
% 3.53/1.85  Reduction            : 0.15
% 3.53/1.85  Demodulation         : 0.10
% 3.53/1.85  BG Simplification    : 0.02
% 3.53/1.85  Subsumption          : 0.10
% 3.53/1.85  Abstraction          : 0.02
% 3.53/1.85  MUC search           : 0.00
% 3.53/1.85  Cooper               : 0.00
% 3.53/1.85  Total                : 0.97
% 3.53/1.85  Index Insertion      : 0.00
% 3.53/1.85  Index Deletion       : 0.00
% 3.53/1.85  Index Matching       : 0.00
% 3.53/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
