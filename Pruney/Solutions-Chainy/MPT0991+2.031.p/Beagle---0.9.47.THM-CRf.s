%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:30 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 261 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 827 expanded)
%              Number of equality atoms :   24 ( 148 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_65,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_32,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    ! [A_18] : k6_relat_1(A_18) = k6_partfun1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_359,plain,(
    ! [D_77,C_79,B_74,E_76,F_78,A_75] :
      ( m1_subset_1(k1_partfun1(A_75,B_74,C_79,D_77,E_76,F_78),k1_zfmisc_1(k2_zfmisc_1(A_75,D_77)))
      | ~ m1_subset_1(F_78,k1_zfmisc_1(k2_zfmisc_1(C_79,D_77)))
      | ~ v1_funct_1(F_78)
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74)))
      | ~ v1_funct_1(E_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k6_relat_1(A_11),k1_zfmisc_1(k2_zfmisc_1(A_11,A_11))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [A_11] : m1_subset_1(k6_partfun1(A_11),k1_zfmisc_1(k2_zfmisc_1(A_11,A_11))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20])).

tff(c_34,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_199,plain,(
    ! [D_43,C_44,A_45,B_46] :
      ( D_43 = C_44
      | ~ r2_relset_1(A_45,B_46,C_44,D_43)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_209,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34,c_199])).

tff(c_228,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_209])).

tff(c_251,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_367,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_359,c_251])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_36,c_367])).

tff(c_385,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_761,plain,(
    ! [B_161,C_160,E_163,A_162,D_164] :
      ( k1_xboole_0 = C_160
      | v2_funct_1(D_164)
      | ~ v2_funct_1(k1_partfun1(A_162,B_161,B_161,C_160,D_164,E_163))
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(B_161,C_160)))
      | ~ v1_funct_2(E_163,B_161,C_160)
      | ~ v1_funct_1(E_163)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161)))
      | ~ v1_funct_2(D_164,A_162,B_161)
      | ~ v1_funct_1(D_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_763,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_761])).

tff(c_765,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_38,c_36,c_50,c_763])).

tff(c_766,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_765])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20])).

tff(c_107,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_107,c_10])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_128,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_50])).

tff(c_784,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_128])).

tff(c_787,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_766,c_8])).

tff(c_87,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_887,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_99])).

tff(c_964,plain,(
    ! [A_173] :
      ( A_173 = '#skF_1'
      | ~ r1_tarski(A_173,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_766,c_2])).

tff(c_974,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_887,c_964])).

tff(c_987,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_32])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.62  
% 3.52/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.63  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.52/1.63  
% 3.52/1.63  %Foreground sorts:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Background operators:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Foreground operators:
% 3.52/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.52/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.63  
% 3.90/1.64  tff(f_110, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 3.90/1.64  tff(f_65, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.90/1.64  tff(f_41, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 3.90/1.64  tff(f_63, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.90/1.64  tff(f_51, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.90/1.64  tff(f_49, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.90/1.64  tff(f_87, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.90/1.64  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.90/1.64  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.90/1.64  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.90/1.64  tff(c_32, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_26, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.90/1.64  tff(c_14, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.90/1.64  tff(c_50, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14])).
% 3.90/1.64  tff(c_359, plain, (![D_77, C_79, B_74, E_76, F_78, A_75]: (m1_subset_1(k1_partfun1(A_75, B_74, C_79, D_77, E_76, F_78), k1_zfmisc_1(k2_zfmisc_1(A_75, D_77))) | ~m1_subset_1(F_78, k1_zfmisc_1(k2_zfmisc_1(C_79, D_77))) | ~v1_funct_1(F_78) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))) | ~v1_funct_1(E_76))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.90/1.64  tff(c_20, plain, (![A_11]: (m1_subset_1(k6_relat_1(A_11), k1_zfmisc_1(k2_zfmisc_1(A_11, A_11))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.90/1.64  tff(c_49, plain, (![A_11]: (m1_subset_1(k6_partfun1(A_11), k1_zfmisc_1(k2_zfmisc_1(A_11, A_11))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20])).
% 3.90/1.64  tff(c_34, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_199, plain, (![D_43, C_44, A_45, B_46]: (D_43=C_44 | ~r2_relset_1(A_45, B_46, C_44, D_43) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.90/1.64  tff(c_209, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_34, c_199])).
% 3.90/1.64  tff(c_228, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_209])).
% 3.90/1.64  tff(c_251, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_228])).
% 3.90/1.64  tff(c_367, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_359, c_251])).
% 3.90/1.64  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_36, c_367])).
% 3.90/1.64  tff(c_385, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_228])).
% 3.90/1.64  tff(c_761, plain, (![B_161, C_160, E_163, A_162, D_164]: (k1_xboole_0=C_160 | v2_funct_1(D_164) | ~v2_funct_1(k1_partfun1(A_162, B_161, B_161, C_160, D_164, E_163)) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(B_161, C_160))) | ~v1_funct_2(E_163, B_161, C_160) | ~v1_funct_1(E_163) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))) | ~v1_funct_2(D_164, A_162, B_161) | ~v1_funct_1(D_164))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.90/1.64  tff(c_763, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_385, c_761])).
% 3.90/1.64  tff(c_765, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_38, c_36, c_50, c_763])).
% 3.90/1.64  tff(c_766, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_32, c_765])).
% 3.90/1.64  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.64  tff(c_100, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20])).
% 3.90/1.64  tff(c_107, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_100])).
% 3.90/1.64  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/1.64  tff(c_116, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_10])).
% 3.90/1.64  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.90/1.64  tff(c_120, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_116, c_2])).
% 3.90/1.64  tff(c_128, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_120, c_50])).
% 3.90/1.64  tff(c_784, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_766, c_128])).
% 3.90/1.64  tff(c_787, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_766, c_766, c_8])).
% 3.90/1.64  tff(c_87, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/1.64  tff(c_99, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_87])).
% 3.90/1.64  tff(c_887, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_787, c_99])).
% 3.90/1.64  tff(c_964, plain, (![A_173]: (A_173='#skF_1' | ~r1_tarski(A_173, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_766, c_766, c_2])).
% 3.90/1.64  tff(c_974, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_887, c_964])).
% 3.90/1.64  tff(c_987, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_32])).
% 3.90/1.64  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_784, c_987])).
% 3.90/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.64  
% 3.90/1.64  Inference rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Ref     : 0
% 3.90/1.64  #Sup     : 203
% 3.90/1.64  #Fact    : 0
% 3.90/1.64  #Define  : 0
% 3.90/1.64  #Split   : 3
% 3.90/1.64  #Chain   : 0
% 3.90/1.64  #Close   : 0
% 3.90/1.64  
% 3.90/1.64  Ordering : KBO
% 3.90/1.64  
% 3.90/1.64  Simplification rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Subsume      : 17
% 3.90/1.64  #Demod        : 259
% 3.90/1.64  #Tautology    : 72
% 3.90/1.64  #SimpNegUnit  : 3
% 3.90/1.64  #BackRed      : 71
% 3.90/1.64  
% 3.90/1.64  #Partial instantiations: 0
% 3.90/1.64  #Strategies tried      : 1
% 3.90/1.64  
% 3.90/1.64  Timing (in seconds)
% 3.90/1.64  ----------------------
% 3.90/1.65  Preprocessing        : 0.33
% 3.90/1.65  Parsing              : 0.17
% 3.90/1.65  CNF conversion       : 0.02
% 3.90/1.65  Main loop            : 0.54
% 3.90/1.65  Inferencing          : 0.19
% 3.90/1.65  Reduction            : 0.19
% 3.90/1.65  Demodulation         : 0.14
% 3.90/1.65  BG Simplification    : 0.02
% 3.90/1.65  Subsumption          : 0.09
% 3.90/1.65  Abstraction          : 0.02
% 3.90/1.65  MUC search           : 0.00
% 3.90/1.65  Cooper               : 0.00
% 3.90/1.65  Total                : 0.91
% 3.90/1.65  Index Insertion      : 0.00
% 3.90/1.65  Index Deletion       : 0.00
% 3.90/1.65  Index Matching       : 0.00
% 3.90/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
