%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:47 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 409 expanded)
%              Number of leaves         :   32 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 (1034 expanded)
%              Number of equality atoms :   47 ( 313 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_58,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1234,plain,(
    ! [A_132] :
      ( r1_tarski(A_132,k2_zfmisc_1(k1_relat_1(A_132),k2_relat_1(A_132)))
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1138,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1(A_124,k1_zfmisc_1(B_125))
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,k2_zfmisc_1(k1_relat_1(A_14),k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_312,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_405,plain,(
    ! [A_75,B_76,A_77] :
      ( k1_relset_1(A_75,B_76,A_77) = k1_relat_1(A_77)
      | ~ r1_tarski(A_77,k2_zfmisc_1(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_24,c_312])).

tff(c_428,plain,(
    ! [A_14] :
      ( k1_relset_1(k1_relat_1(A_14),k2_relat_1(A_14),A_14) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_30,c_405])).

tff(c_514,plain,(
    ! [B_84,C_85,A_86] :
      ( k1_xboole_0 = B_84
      | v1_funct_2(C_85,A_86,B_84)
      | k1_relset_1(A_86,B_84,C_85) != A_86
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_719,plain,(
    ! [B_105,A_106,A_107] :
      ( k1_xboole_0 = B_105
      | v1_funct_2(A_106,A_107,B_105)
      | k1_relset_1(A_107,B_105,A_106) != A_107
      | ~ r1_tarski(A_106,k2_zfmisc_1(A_107,B_105)) ) ),
    inference(resolution,[status(thm)],[c_24,c_514])).

tff(c_814,plain,(
    ! [A_111] :
      ( k2_relat_1(A_111) = k1_xboole_0
      | v1_funct_2(A_111,k1_relat_1(A_111),k2_relat_1(A_111))
      | k1_relset_1(k1_relat_1(A_111),k2_relat_1(A_111),A_111) != k1_relat_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_30,c_719])).

tff(c_56,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54])).

tff(c_89,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_821,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_814,c_89])).

tff(c_839,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_821])).

tff(c_848,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_839])).

tff(c_851,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_848])).

tff(c_855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_851])).

tff(c_856,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_257,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47)))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_272,plain,(
    ! [A_47] :
      ( k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47)) = A_47
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47)),A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(resolution,[status(thm)],[c_257,c_6])).

tff(c_865,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_272])).

tff(c_880,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12,c_16,c_16,c_856,c_865])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_121,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k2_relat_1(A_36))
      | ~ v1_relat_1(A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_124,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | v1_xboole_0(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_121])).

tff(c_127,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(A_37)
      | v1_xboole_0(k6_relat_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_124])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_142,plain,(
    ! [A_40] :
      ( k6_relat_1(A_40) = k1_xboole_0
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_150,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_142])).

tff(c_32,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_160,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_32])).

tff(c_20,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_320,plain,(
    ! [A_54,B_55] : k1_relset_1(A_54,B_55,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_312])).

tff(c_329,plain,(
    ! [A_54,B_55] : k1_relset_1(A_54,B_55,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_320])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_567,plain,(
    ! [C_90,B_91] :
      ( v1_funct_2(C_90,k1_xboole_0,B_91)
      | k1_relset_1(k1_xboole_0,B_91,C_90) != k1_xboole_0
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_46])).

tff(c_573,plain,(
    ! [B_91] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_91)
      | k1_relset_1(k1_xboole_0,B_91,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_567])).

tff(c_577,plain,(
    ! [B_91] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_573])).

tff(c_899,plain,(
    ! [B_91] : v1_funct_2('#skF_1','#skF_1',B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_880,c_577])).

tff(c_916,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_880,c_160])).

tff(c_858,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_89])).

tff(c_888,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_858])).

tff(c_1028,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_888])).

tff(c_1060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_1028])).

tff(c_1061,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1146,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1138,c_1061])).

tff(c_1239,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1234,c_1146])).

tff(c_1256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:48:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.14/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.48  
% 3.21/1.50  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.21/1.50  tff(f_68, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.21/1.50  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.50  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.50  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.21/1.50  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.21/1.50  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.21/1.50  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.21/1.50  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.21/1.50  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.21/1.50  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.21/1.50  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.21/1.50  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.21/1.50  tff(c_58, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.21/1.50  tff(c_1234, plain, (![A_132]: (r1_tarski(A_132, k2_zfmisc_1(k1_relat_1(A_132), k2_relat_1(A_132))) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.50  tff(c_1138, plain, (![A_124, B_125]: (m1_subset_1(A_124, k1_zfmisc_1(B_125)) | ~r1_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.50  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.50  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.21/1.50  tff(c_30, plain, (![A_14]: (r1_tarski(A_14, k2_zfmisc_1(k1_relat_1(A_14), k2_relat_1(A_14))) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.50  tff(c_24, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.50  tff(c_312, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.50  tff(c_405, plain, (![A_75, B_76, A_77]: (k1_relset_1(A_75, B_76, A_77)=k1_relat_1(A_77) | ~r1_tarski(A_77, k2_zfmisc_1(A_75, B_76)))), inference(resolution, [status(thm)], [c_24, c_312])).
% 3.21/1.50  tff(c_428, plain, (![A_14]: (k1_relset_1(k1_relat_1(A_14), k2_relat_1(A_14), A_14)=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_30, c_405])).
% 3.21/1.50  tff(c_514, plain, (![B_84, C_85, A_86]: (k1_xboole_0=B_84 | v1_funct_2(C_85, A_86, B_84) | k1_relset_1(A_86, B_84, C_85)!=A_86 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_84))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.21/1.50  tff(c_719, plain, (![B_105, A_106, A_107]: (k1_xboole_0=B_105 | v1_funct_2(A_106, A_107, B_105) | k1_relset_1(A_107, B_105, A_106)!=A_107 | ~r1_tarski(A_106, k2_zfmisc_1(A_107, B_105)))), inference(resolution, [status(thm)], [c_24, c_514])).
% 3.21/1.50  tff(c_814, plain, (![A_111]: (k2_relat_1(A_111)=k1_xboole_0 | v1_funct_2(A_111, k1_relat_1(A_111), k2_relat_1(A_111)) | k1_relset_1(k1_relat_1(A_111), k2_relat_1(A_111), A_111)!=k1_relat_1(A_111) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_30, c_719])).
% 3.21/1.50  tff(c_56, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.21/1.50  tff(c_54, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.21/1.50  tff(c_60, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54])).
% 3.21/1.50  tff(c_89, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.21/1.50  tff(c_821, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_814, c_89])).
% 3.21/1.50  tff(c_839, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_821])).
% 3.21/1.50  tff(c_848, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_839])).
% 3.21/1.50  tff(c_851, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_428, c_848])).
% 3.21/1.50  tff(c_855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_851])).
% 3.21/1.50  tff(c_856, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_839])).
% 3.21/1.50  tff(c_257, plain, (![A_47]: (r1_tarski(A_47, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47))) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.50  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.21/1.50  tff(c_272, plain, (![A_47]: (k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47))=A_47 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47)), A_47) | ~v1_relat_1(A_47))), inference(resolution, [status(thm)], [c_257, c_6])).
% 3.21/1.50  tff(c_865, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_856, c_272])).
% 3.21/1.50  tff(c_880, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12, c_16, c_16, c_856, c_865])).
% 3.21/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.21/1.50  tff(c_36, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.21/1.50  tff(c_34, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.50  tff(c_121, plain, (![A_36]: (~v1_xboole_0(k2_relat_1(A_36)) | ~v1_relat_1(A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.21/1.50  tff(c_124, plain, (![A_15]: (~v1_xboole_0(A_15) | ~v1_relat_1(k6_relat_1(A_15)) | v1_xboole_0(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_121])).
% 3.21/1.50  tff(c_127, plain, (![A_37]: (~v1_xboole_0(A_37) | v1_xboole_0(k6_relat_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_124])).
% 3.21/1.50  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.21/1.50  tff(c_142, plain, (![A_40]: (k6_relat_1(A_40)=k1_xboole_0 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_127, c_4])).
% 3.21/1.50  tff(c_150, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_142])).
% 3.21/1.50  tff(c_32, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.50  tff(c_160, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_150, c_32])).
% 3.21/1.50  tff(c_20, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.50  tff(c_320, plain, (![A_54, B_55]: (k1_relset_1(A_54, B_55, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_312])).
% 3.21/1.50  tff(c_329, plain, (![A_54, B_55]: (k1_relset_1(A_54, B_55, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_320])).
% 3.21/1.50  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.21/1.50  tff(c_46, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.21/1.50  tff(c_567, plain, (![C_90, B_91]: (v1_funct_2(C_90, k1_xboole_0, B_91) | k1_relset_1(k1_xboole_0, B_91, C_90)!=k1_xboole_0 | ~m1_subset_1(C_90, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_46])).
% 3.21/1.50  tff(c_573, plain, (![B_91]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_91) | k1_relset_1(k1_xboole_0, B_91, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_567])).
% 3.21/1.50  tff(c_577, plain, (![B_91]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_573])).
% 3.21/1.50  tff(c_899, plain, (![B_91]: (v1_funct_2('#skF_1', '#skF_1', B_91))), inference(demodulation, [status(thm), theory('equality')], [c_880, c_880, c_577])).
% 3.21/1.50  tff(c_916, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_880, c_880, c_160])).
% 3.21/1.50  tff(c_858, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_856, c_89])).
% 3.21/1.50  tff(c_888, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_880, c_858])).
% 3.21/1.50  tff(c_1028, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_888])).
% 3.21/1.50  tff(c_1060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_899, c_1028])).
% 3.21/1.50  tff(c_1061, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_60])).
% 3.21/1.50  tff(c_1146, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_1138, c_1061])).
% 3.21/1.50  tff(c_1239, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1234, c_1146])).
% 3.21/1.50  tff(c_1256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1239])).
% 3.21/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  Inference rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Ref     : 0
% 3.21/1.50  #Sup     : 249
% 3.21/1.50  #Fact    : 0
% 3.21/1.50  #Define  : 0
% 3.21/1.50  #Split   : 2
% 3.21/1.50  #Chain   : 0
% 3.21/1.50  #Close   : 0
% 3.21/1.50  
% 3.21/1.50  Ordering : KBO
% 3.21/1.50  
% 3.21/1.50  Simplification rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Subsume      : 21
% 3.21/1.50  #Demod        : 372
% 3.21/1.50  #Tautology    : 164
% 3.21/1.50  #SimpNegUnit  : 0
% 3.21/1.50  #BackRed      : 42
% 3.21/1.50  
% 3.21/1.50  #Partial instantiations: 0
% 3.21/1.50  #Strategies tried      : 1
% 3.21/1.50  
% 3.21/1.50  Timing (in seconds)
% 3.21/1.50  ----------------------
% 3.21/1.50  Preprocessing        : 0.32
% 3.21/1.50  Parsing              : 0.17
% 3.21/1.50  CNF conversion       : 0.02
% 3.21/1.50  Main loop            : 0.40
% 3.21/1.50  Inferencing          : 0.15
% 3.21/1.50  Reduction            : 0.13
% 3.21/1.50  Demodulation         : 0.10
% 3.21/1.50  BG Simplification    : 0.02
% 3.21/1.50  Subsumption          : 0.07
% 3.21/1.50  Abstraction          : 0.02
% 3.21/1.50  MUC search           : 0.00
% 3.21/1.50  Cooper               : 0.00
% 3.21/1.50  Total                : 0.76
% 3.21/1.50  Index Insertion      : 0.00
% 3.21/1.50  Index Deletion       : 0.00
% 3.21/1.50  Index Matching       : 0.00
% 3.21/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
