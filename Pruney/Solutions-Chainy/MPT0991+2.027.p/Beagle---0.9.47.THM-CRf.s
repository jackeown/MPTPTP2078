%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:30 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 169 expanded)
%              Number of leaves         :   43 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 480 expanded)
%              Number of equality atoms :   33 (  74 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => ( v2_funct_1(C)
        <=> ! [D,E] :
              ( ( r2_hidden(D,A)
                & r2_hidden(E,A)
                & k1_funct_1(C,D) = k1_funct_1(C,E) )
             => D = E ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

tff(f_94,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_28,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_64,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_668,plain,(
    ! [B_162,A_163,C_164] :
      ( k1_xboole_0 = B_162
      | r2_hidden('#skF_1'(A_163,B_162,C_164),A_163)
      | v2_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162)))
      | ~ v1_funct_2(C_164,A_163,B_162)
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_677,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_668])).

tff(c_686,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_677])).

tff(c_687,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_74,c_686])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_38,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24])).

tff(c_419,plain,(
    ! [E_127,D_131,A_128,B_130,F_126,C_129] :
      ( k1_partfun1(A_128,B_130,C_129,D_131,E_127,F_126) = k5_relat_1(E_127,F_126)
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_129,D_131)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_130)))
      | ~ v1_funct_1(E_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_423,plain,(
    ! [A_128,B_130,E_127] :
      ( k1_partfun1(A_128,B_130,'#skF_4','#skF_3',E_127,'#skF_6') = k5_relat_1(E_127,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_130)))
      | ~ v1_funct_1(E_127) ) ),
    inference(resolution,[status(thm)],[c_68,c_419])).

tff(c_440,plain,(
    ! [A_136,B_137,E_138] :
      ( k1_partfun1(A_136,B_137,'#skF_4','#skF_3',E_138,'#skF_6') = k5_relat_1(E_138,'#skF_6')
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_1(E_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_423])).

tff(c_453,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_440])).

tff(c_461,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_453])).

tff(c_30,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_81,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30])).

tff(c_66,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_204,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_214,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_66,c_204])).

tff(c_233,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_214])).

tff(c_259,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_468,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_259])).

tff(c_548,plain,(
    ! [C_154,E_155,D_157,F_156,A_153,B_158] :
      ( m1_subset_1(k1_partfun1(A_153,B_158,C_154,D_157,E_155,F_156),k1_zfmisc_1(k2_zfmisc_1(A_153,D_157)))
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(C_154,D_157)))
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_158)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_606,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_548])).

tff(c_635,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_72,c_68,c_606])).

tff(c_637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_635])).

tff(c_638,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_1464,plain,(
    ! [C_234,D_233,A_237,E_236,B_235] :
      ( k1_xboole_0 = C_234
      | v2_funct_1(D_233)
      | ~ v2_funct_1(k1_partfun1(A_237,B_235,B_235,C_234,D_233,E_236))
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(B_235,C_234)))
      | ~ v1_funct_2(E_236,B_235,C_234)
      | ~ v1_funct_1(E_236)
      | ~ m1_subset_1(D_233,k1_zfmisc_1(k2_zfmisc_1(A_237,B_235)))
      | ~ v1_funct_2(D_233,A_237,B_235)
      | ~ v1_funct_1(D_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1470,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_1464])).

tff(c_1477,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_72,c_70,c_68,c_82,c_1470])).

tff(c_1478,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1477])).

tff(c_4,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_112,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [A_3] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_136,plain,(
    ! [A_3] : ~ v1_relat_1(A_3) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_115,plain,(
    ! [A_21] :
      ( v1_relat_1(k6_partfun1(A_21))
      | ~ v1_relat_1(k2_zfmisc_1(A_21,A_21)) ) ),
    inference(resolution,[status(thm)],[c_81,c_112])).

tff(c_127,plain,(
    ! [A_21] : v1_relat_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_115])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_127])).

tff(c_143,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_12] : k7_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(A_78,B_79)
      | ~ r2_hidden(A_78,k1_relat_1(k7_relat_1(C_80,B_79)))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_180,plain,(
    ! [A_78,A_12] :
      ( r2_hidden(A_78,A_12)
      | ~ r2_hidden(A_78,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_177])).

tff(c_182,plain,(
    ! [A_78,A_12] :
      ( r2_hidden(A_78,A_12)
      | ~ r2_hidden(A_78,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_16,c_180])).

tff(c_1599,plain,(
    ! [A_248,A_249] :
      ( r2_hidden(A_248,A_249)
      | ~ r2_hidden(A_248,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_182])).

tff(c_1753,plain,(
    ! [A_258] : r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),A_258) ),
    inference(resolution,[status(thm)],[c_687,c_1599])).

tff(c_2,plain,(
    ! [A_1,B_2] : ~ r2_hidden(A_1,k2_zfmisc_1(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1809,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1753,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/2.35  
% 5.07/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/2.35  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.07/2.35  
% 5.07/2.35  %Foreground sorts:
% 5.07/2.35  
% 5.07/2.35  
% 5.07/2.35  %Background operators:
% 5.07/2.35  
% 5.07/2.35  
% 5.07/2.35  %Foreground operators:
% 5.07/2.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.07/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.07/2.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.07/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/2.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.07/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.07/2.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.07/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.07/2.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.07/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.07/2.35  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.35  tff('#skF_5', type, '#skF_5': $i).
% 5.07/2.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.07/2.35  tff('#skF_6', type, '#skF_6': $i).
% 5.07/2.35  tff('#skF_3', type, '#skF_3': $i).
% 5.07/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.07/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.07/2.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.07/2.35  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.07/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.07/2.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.07/2.35  tff('#skF_4', type, '#skF_4': $i).
% 5.07/2.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.07/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.07/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.07/2.35  
% 5.07/2.37  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 5.07/2.37  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (v2_funct_1(C) <=> (![D, E]: (((r2_hidden(D, A) & r2_hidden(E, A)) & (k1_funct_1(C, D) = k1_funct_1(C, E))) => (D = E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_2)).
% 5.07/2.37  tff(f_94, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.07/2.37  tff(f_60, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 5.07/2.37  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.07/2.37  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.07/2.37  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.07/2.37  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.07/2.37  tff(f_137, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.07/2.37  tff(f_30, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.07/2.37  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.07/2.37  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.07/2.37  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.07/2.37  tff(f_47, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 5.07/2.37  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 5.07/2.37  tff(f_28, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.07/2.37  tff(c_64, plain, (~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_74, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_668, plain, (![B_162, A_163, C_164]: (k1_xboole_0=B_162 | r2_hidden('#skF_1'(A_163, B_162, C_164), A_163) | v2_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))) | ~v1_funct_2(C_164, A_163, B_162) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.07/2.37  tff(c_677, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_668])).
% 5.07/2.37  tff(c_686, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_677])).
% 5.07/2.37  tff(c_687, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_74, c_686])).
% 5.07/2.37  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_38, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.07/2.37  tff(c_24, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.07/2.37  tff(c_82, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_24])).
% 5.07/2.37  tff(c_419, plain, (![E_127, D_131, A_128, B_130, F_126, C_129]: (k1_partfun1(A_128, B_130, C_129, D_131, E_127, F_126)=k5_relat_1(E_127, F_126) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_129, D_131))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_130))) | ~v1_funct_1(E_127))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.07/2.37  tff(c_423, plain, (![A_128, B_130, E_127]: (k1_partfun1(A_128, B_130, '#skF_4', '#skF_3', E_127, '#skF_6')=k5_relat_1(E_127, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_130))) | ~v1_funct_1(E_127))), inference(resolution, [status(thm)], [c_68, c_419])).
% 5.07/2.37  tff(c_440, plain, (![A_136, B_137, E_138]: (k1_partfun1(A_136, B_137, '#skF_4', '#skF_3', E_138, '#skF_6')=k5_relat_1(E_138, '#skF_6') | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_1(E_138))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_423])).
% 5.07/2.37  tff(c_453, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_440])).
% 5.07/2.37  tff(c_461, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_453])).
% 5.07/2.37  tff(c_30, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.07/2.37  tff(c_81, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30])).
% 5.07/2.37  tff(c_66, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.07/2.37  tff(c_204, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.07/2.37  tff(c_214, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_66, c_204])).
% 5.07/2.37  tff(c_233, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_214])).
% 5.07/2.37  tff(c_259, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_233])).
% 5.07/2.37  tff(c_468, plain, (~m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_259])).
% 5.07/2.37  tff(c_548, plain, (![C_154, E_155, D_157, F_156, A_153, B_158]: (m1_subset_1(k1_partfun1(A_153, B_158, C_154, D_157, E_155, F_156), k1_zfmisc_1(k2_zfmisc_1(A_153, D_157))) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(C_154, D_157))) | ~v1_funct_1(F_156) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_158))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.07/2.37  tff(c_606, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_461, c_548])).
% 5.07/2.37  tff(c_635, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_72, c_68, c_606])).
% 5.07/2.37  tff(c_637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_468, c_635])).
% 5.07/2.37  tff(c_638, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_233])).
% 5.07/2.37  tff(c_1464, plain, (![C_234, D_233, A_237, E_236, B_235]: (k1_xboole_0=C_234 | v2_funct_1(D_233) | ~v2_funct_1(k1_partfun1(A_237, B_235, B_235, C_234, D_233, E_236)) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(B_235, C_234))) | ~v1_funct_2(E_236, B_235, C_234) | ~v1_funct_1(E_236) | ~m1_subset_1(D_233, k1_zfmisc_1(k2_zfmisc_1(A_237, B_235))) | ~v1_funct_2(D_233, A_237, B_235) | ~v1_funct_1(D_233))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.07/2.37  tff(c_1470, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_638, c_1464])).
% 5.07/2.37  tff(c_1477, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_72, c_70, c_68, c_82, c_1470])).
% 5.07/2.37  tff(c_1478, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_64, c_1477])).
% 5.07/2.37  tff(c_4, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.07/2.37  tff(c_112, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.07/2.37  tff(c_131, plain, (![A_3]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_4, c_112])).
% 5.07/2.37  tff(c_136, plain, (![A_3]: (~v1_relat_1(A_3))), inference(splitLeft, [status(thm)], [c_131])).
% 5.07/2.37  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.07/2.37  tff(c_115, plain, (![A_21]: (v1_relat_1(k6_partfun1(A_21)) | ~v1_relat_1(k2_zfmisc_1(A_21, A_21)))), inference(resolution, [status(thm)], [c_81, c_112])).
% 5.07/2.37  tff(c_127, plain, (![A_21]: (v1_relat_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_115])).
% 5.07/2.37  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_127])).
% 5.07/2.37  tff(c_143, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_131])).
% 5.07/2.37  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.07/2.37  tff(c_12, plain, (![A_12]: (k7_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.07/2.37  tff(c_177, plain, (![A_78, B_79, C_80]: (r2_hidden(A_78, B_79) | ~r2_hidden(A_78, k1_relat_1(k7_relat_1(C_80, B_79))) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.07/2.37  tff(c_180, plain, (![A_78, A_12]: (r2_hidden(A_78, A_12) | ~r2_hidden(A_78, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_177])).
% 5.07/2.37  tff(c_182, plain, (![A_78, A_12]: (r2_hidden(A_78, A_12) | ~r2_hidden(A_78, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_16, c_180])).
% 5.07/2.37  tff(c_1599, plain, (![A_248, A_249]: (r2_hidden(A_248, A_249) | ~r2_hidden(A_248, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_182])).
% 5.07/2.37  tff(c_1753, plain, (![A_258]: (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), A_258))), inference(resolution, [status(thm)], [c_687, c_1599])).
% 5.07/2.37  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden(A_1, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.07/2.37  tff(c_1809, plain, $false, inference(resolution, [status(thm)], [c_1753, c_2])).
% 5.07/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/2.37  
% 5.07/2.37  Inference rules
% 5.07/2.37  ----------------------
% 5.07/2.37  #Ref     : 2
% 5.07/2.37  #Sup     : 353
% 5.07/2.37  #Fact    : 0
% 5.07/2.37  #Define  : 0
% 5.07/2.37  #Split   : 7
% 5.07/2.37  #Chain   : 0
% 5.07/2.37  #Close   : 0
% 5.07/2.37  
% 5.07/2.37  Ordering : KBO
% 5.07/2.37  
% 5.07/2.37  Simplification rules
% 5.07/2.37  ----------------------
% 5.07/2.37  #Subsume      : 50
% 5.07/2.37  #Demod        : 316
% 5.07/2.37  #Tautology    : 93
% 5.07/2.37  #SimpNegUnit  : 28
% 5.07/2.37  #BackRed      : 38
% 5.07/2.37  
% 5.07/2.37  #Partial instantiations: 0
% 5.07/2.37  #Strategies tried      : 1
% 5.07/2.37  
% 5.07/2.37  Timing (in seconds)
% 5.07/2.37  ----------------------
% 5.07/2.37  Preprocessing        : 0.59
% 5.07/2.37  Parsing              : 0.29
% 5.07/2.37  CNF conversion       : 0.05
% 5.07/2.37  Main loop            : 0.84
% 5.07/2.37  Inferencing          : 0.27
% 5.07/2.37  Reduction            : 0.32
% 5.07/2.37  Demodulation         : 0.23
% 5.07/2.37  BG Simplification    : 0.05
% 5.07/2.37  Subsumption          : 0.14
% 5.07/2.37  Abstraction          : 0.04
% 5.07/2.37  MUC search           : 0.00
% 5.07/2.37  Cooper               : 0.00
% 5.07/2.37  Total                : 1.47
% 5.07/2.37  Index Insertion      : 0.00
% 5.07/2.37  Index Deletion       : 0.00
% 5.07/2.38  Index Matching       : 0.00
% 5.07/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
