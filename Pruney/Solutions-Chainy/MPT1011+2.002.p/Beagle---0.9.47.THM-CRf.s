%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:33 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 187 expanded)
%              Number of leaves         :   43 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 487 expanded)
%              Number of equality atoms :   35 (  71 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,k1_tarski(B))
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => r2_relset_1(A,k1_tarski(B),C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_196,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_226,plain,(
    ! [B_91,A_92] :
      ( k4_xboole_0(B_91,A_92) = k3_subset_1(B_91,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(resolution,[status(thm)],[c_50,c_196])).

tff(c_235,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = k3_subset_1(A_5,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_244,plain,(
    ! [A_93] : k3_subset_1(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_186,plain,(
    ! [A_85,B_86] :
      ( k3_subset_1(A_85,k3_subset_1(A_85,B_86)) = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_195,plain,(
    ! [B_47,A_46] :
      ( k3_subset_1(B_47,k3_subset_1(B_47,A_46)) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_50,c_186])).

tff(c_250,plain,(
    ! [A_93] :
      ( k3_subset_1(A_93,A_93) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_195])).

tff(c_256,plain,(
    ! [A_93] : k3_subset_1(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_250])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_226])).

tff(c_284,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_243])).

tff(c_40,plain,(
    ! [B_41] : k4_xboole_0(k1_tarski(B_41),k1_tarski(B_41)) != k1_tarski(B_41) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_285,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_40])).

tff(c_463,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( r2_hidden('#skF_3'(A_141,B_142,C_143,D_144),A_141)
      | r2_relset_1(A_141,B_142,C_143,D_144)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_2(D_144,A_141,B_142)
      | ~ v1_funct_1(D_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_2(C_143,A_141,B_142)
      | ~ v1_funct_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_467,plain,(
    ! [C_143] :
      ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),C_143,'#skF_7'),'#skF_4')
      | r2_relset_1('#skF_4',k1_tarski('#skF_5'),C_143,'#skF_7')
      | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
      | ~ v1_funct_2(C_143,'#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1(C_143) ) ),
    inference(resolution,[status(thm)],[c_60,c_463])).

tff(c_480,plain,(
    ! [C_147] :
      ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),C_147,'#skF_7'),'#skF_4')
      | r2_relset_1('#skF_4',k1_tarski('#skF_5'),C_147,'#skF_7')
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
      | ~ v1_funct_2(C_147,'#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1(C_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_467])).

tff(c_483,plain,
    ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4')
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_480])).

tff(c_493,plain,
    ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4')
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_483])).

tff(c_494,plain,(
    r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_493])).

tff(c_56,plain,(
    ! [D_59,C_58,B_57,A_56] :
      ( r2_hidden(k1_funct_1(D_59,C_58),B_57)
      | k1_xboole_0 = B_57
      | ~ r2_hidden(C_58,A_56)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_2(D_59,A_56,B_57)
      | ~ v1_funct_1(D_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_503,plain,(
    ! [D_148,B_149] :
      ( r2_hidden(k1_funct_1(D_148,'#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')),B_149)
      | k1_xboole_0 = B_149
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_149)))
      | ~ v1_funct_2(D_148,'#skF_4',B_149)
      | ~ v1_funct_1(D_148) ) ),
    inference(resolution,[status(thm)],[c_494,c_56])).

tff(c_14,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_509,plain,(
    ! [D_148,A_7] :
      ( k1_funct_1(D_148,'#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = A_7
      | k1_tarski(A_7) = k1_xboole_0
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski(A_7))))
      | ~ v1_funct_2(D_148,'#skF_4',k1_tarski(A_7))
      | ~ v1_funct_1(D_148) ) ),
    inference(resolution,[status(thm)],[c_503,c_14])).

tff(c_514,plain,(
    ! [D_150,A_151] :
      ( k1_funct_1(D_150,'#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = A_151
      | ~ m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski(A_151))))
      | ~ v1_funct_2(D_150,'#skF_4',k1_tarski(A_151))
      | ~ v1_funct_1(D_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_509])).

tff(c_517,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_514])).

tff(c_527,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_517])).

tff(c_520,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_514])).

tff(c_530,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_520])).

tff(c_52,plain,(
    ! [D_54,A_48,B_49,C_50] :
      ( k1_funct_1(D_54,'#skF_3'(A_48,B_49,C_50,D_54)) != k1_funct_1(C_50,'#skF_3'(A_48,B_49,C_50,D_54))
      | r2_relset_1(A_48,B_49,C_50,D_54)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(D_54,A_48,B_49)
      | ~ v1_funct_1(D_54)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_547,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) != '#skF_5'
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_52])).

tff(c_554,plain,(
    r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_527,c_547])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.44  
% 2.90/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.44  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.44  
% 2.90/1.44  %Foreground sorts:
% 2.90/1.44  
% 2.90/1.44  
% 2.90/1.44  %Background operators:
% 2.90/1.44  
% 2.90/1.44  
% 2.90/1.44  %Foreground operators:
% 2.90/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.90/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.90/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.90/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.90/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.90/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.90/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.90/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.90/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.90/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.90/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.90/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.44  
% 2.90/1.46  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, k1_tarski(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r2_relset_1(A, k1_tarski(B), C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_2)).
% 2.90/1.46  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.90/1.46  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.90/1.46  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.90/1.46  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.90/1.46  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.90/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.46  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.90/1.46  tff(f_95, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 2.90/1.46  tff(f_107, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.90/1.46  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.90/1.46  tff(c_58, plain, (~r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.90/1.46  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.90/1.46  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.90/1.46  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.90/1.46  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.90/1.46  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.90/1.46  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.90/1.46  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.46  tff(c_12, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.46  tff(c_50, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.46  tff(c_196, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.90/1.46  tff(c_226, plain, (![B_91, A_92]: (k4_xboole_0(B_91, A_92)=k3_subset_1(B_91, A_92) | ~r1_tarski(A_92, B_91))), inference(resolution, [status(thm)], [c_50, c_196])).
% 2.90/1.46  tff(c_235, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=k3_subset_1(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_226])).
% 2.90/1.46  tff(c_244, plain, (![A_93]: (k3_subset_1(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_235])).
% 2.90/1.46  tff(c_186, plain, (![A_85, B_86]: (k3_subset_1(A_85, k3_subset_1(A_85, B_86))=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.46  tff(c_195, plain, (![B_47, A_46]: (k3_subset_1(B_47, k3_subset_1(B_47, A_46))=A_46 | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_50, c_186])).
% 2.90/1.46  tff(c_250, plain, (![A_93]: (k3_subset_1(A_93, A_93)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_93))), inference(superposition, [status(thm), theory('equality')], [c_244, c_195])).
% 2.90/1.46  tff(c_256, plain, (![A_93]: (k3_subset_1(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_250])).
% 2.90/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.46  tff(c_243, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_226])).
% 2.90/1.46  tff(c_284, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_243])).
% 2.90/1.46  tff(c_40, plain, (![B_41]: (k4_xboole_0(k1_tarski(B_41), k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.90/1.46  tff(c_285, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_40])).
% 2.90/1.46  tff(c_463, plain, (![A_141, B_142, C_143, D_144]: (r2_hidden('#skF_3'(A_141, B_142, C_143, D_144), A_141) | r2_relset_1(A_141, B_142, C_143, D_144) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_2(D_144, A_141, B_142) | ~v1_funct_1(D_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_2(C_143, A_141, B_142) | ~v1_funct_1(C_143))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.46  tff(c_467, plain, (![C_143]: (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), C_143, '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), C_143, '#skF_7') | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2(C_143, '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1(C_143))), inference(resolution, [status(thm)], [c_60, c_463])).
% 2.90/1.46  tff(c_480, plain, (![C_147]: (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), C_147, '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), C_147, '#skF_7') | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2(C_147, '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1(C_147))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_467])).
% 2.90/1.46  tff(c_483, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_480])).
% 2.90/1.46  tff(c_493, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_483])).
% 2.90/1.46  tff(c_494, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_493])).
% 2.90/1.46  tff(c_56, plain, (![D_59, C_58, B_57, A_56]: (r2_hidden(k1_funct_1(D_59, C_58), B_57) | k1_xboole_0=B_57 | ~r2_hidden(C_58, A_56) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(D_59, A_56, B_57) | ~v1_funct_1(D_59))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.46  tff(c_503, plain, (![D_148, B_149]: (r2_hidden(k1_funct_1(D_148, '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), B_149) | k1_xboole_0=B_149 | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_149))) | ~v1_funct_2(D_148, '#skF_4', B_149) | ~v1_funct_1(D_148))), inference(resolution, [status(thm)], [c_494, c_56])).
% 2.90/1.46  tff(c_14, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.90/1.46  tff(c_509, plain, (![D_148, A_7]: (k1_funct_1(D_148, '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))=A_7 | k1_tarski(A_7)=k1_xboole_0 | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski(A_7)))) | ~v1_funct_2(D_148, '#skF_4', k1_tarski(A_7)) | ~v1_funct_1(D_148))), inference(resolution, [status(thm)], [c_503, c_14])).
% 2.90/1.46  tff(c_514, plain, (![D_150, A_151]: (k1_funct_1(D_150, '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))=A_151 | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski(A_151)))) | ~v1_funct_2(D_150, '#skF_4', k1_tarski(A_151)) | ~v1_funct_1(D_150))), inference(negUnitSimplification, [status(thm)], [c_285, c_509])).
% 2.90/1.46  tff(c_517, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_514])).
% 2.90/1.46  tff(c_527, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_517])).
% 2.90/1.46  tff(c_520, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_514])).
% 2.90/1.46  tff(c_530, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_520])).
% 2.90/1.46  tff(c_52, plain, (![D_54, A_48, B_49, C_50]: (k1_funct_1(D_54, '#skF_3'(A_48, B_49, C_50, D_54))!=k1_funct_1(C_50, '#skF_3'(A_48, B_49, C_50, D_54)) | r2_relset_1(A_48, B_49, C_50, D_54) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(D_54, A_48, B_49) | ~v1_funct_1(D_54) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.46  tff(c_547, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))!='#skF_5' | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_530, c_52])).
% 2.90/1.46  tff(c_554, plain, (r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_527, c_547])).
% 2.90/1.46  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_554])).
% 2.90/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.46  
% 2.90/1.46  Inference rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Ref     : 1
% 2.90/1.46  #Sup     : 105
% 2.90/1.46  #Fact    : 0
% 2.90/1.46  #Define  : 0
% 2.90/1.46  #Split   : 4
% 2.90/1.46  #Chain   : 0
% 2.90/1.46  #Close   : 0
% 2.90/1.46  
% 2.90/1.46  Ordering : KBO
% 2.90/1.46  
% 2.90/1.46  Simplification rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Subsume      : 0
% 2.90/1.46  #Demod        : 36
% 2.90/1.46  #Tautology    : 68
% 2.90/1.46  #SimpNegUnit  : 3
% 2.90/1.46  #BackRed      : 1
% 2.90/1.46  
% 2.90/1.46  #Partial instantiations: 0
% 2.90/1.46  #Strategies tried      : 1
% 2.90/1.46  
% 2.90/1.46  Timing (in seconds)
% 2.90/1.46  ----------------------
% 2.90/1.46  Preprocessing        : 0.34
% 2.90/1.46  Parsing              : 0.18
% 2.90/1.46  CNF conversion       : 0.02
% 2.90/1.46  Main loop            : 0.30
% 2.90/1.46  Inferencing          : 0.11
% 2.90/1.46  Reduction            : 0.09
% 2.90/1.46  Demodulation         : 0.06
% 2.90/1.46  BG Simplification    : 0.02
% 2.90/1.46  Subsumption          : 0.06
% 2.90/1.46  Abstraction          : 0.02
% 2.90/1.46  MUC search           : 0.00
% 2.90/1.46  Cooper               : 0.00
% 2.90/1.46  Total                : 0.67
% 2.90/1.46  Index Insertion      : 0.00
% 2.90/1.46  Index Deletion       : 0.00
% 2.90/1.46  Index Matching       : 0.00
% 2.90/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
