%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:46 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 698 expanded)
%              Number of leaves         :   24 ( 244 expanded)
%              Depth                    :   14
%              Number of atoms          :  168 (1931 expanded)
%              Number of equality atoms :   48 ( 627 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5587,plain,(
    ! [C_314,A_315,B_316] :
      ( m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | ~ r1_tarski(k2_relat_1(C_314),B_316)
      | ~ r1_tarski(k1_relat_1(C_314),A_315)
      | ~ v1_relat_1(C_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_260,plain,(
    ! [C_51,A_52,B_53] :
      ( m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ r1_tarski(k2_relat_1(C_51),B_53)
      | ~ r1_tarski(k1_relat_1(C_51),A_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_833,plain,(
    ! [C_115,A_116,B_117] :
      ( r1_tarski(C_115,k2_zfmisc_1(A_116,B_117))
      | ~ r1_tarski(k2_relat_1(C_115),B_117)
      | ~ r1_tarski(k1_relat_1(C_115),A_116)
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_260,c_16])).

tff(c_838,plain,(
    ! [C_118,A_119] :
      ( r1_tarski(C_118,k2_zfmisc_1(A_119,k2_relat_1(C_118)))
      | ~ r1_tarski(k1_relat_1(C_118),A_119)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_833])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [A_34,B_35,A_6] :
      ( k1_relset_1(A_34,B_35,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_34,B_35)) ) ),
    inference(resolution,[status(thm)],[c_18,c_131])).

tff(c_866,plain,(
    ! [A_121,C_122] :
      ( k1_relset_1(A_121,k2_relat_1(C_122),C_122) = k1_relat_1(C_122)
      | ~ r1_tarski(k1_relat_1(C_122),A_121)
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_838,c_142])).

tff(c_881,plain,(
    ! [C_122] :
      ( k1_relset_1(k1_relat_1(C_122),k2_relat_1(C_122),C_122) = k1_relat_1(C_122)
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_866])).

tff(c_24,plain,(
    ! [C_16,A_14,B_15] :
      ( m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ r1_tarski(k2_relat_1(C_16),B_15)
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_361,plain,(
    ! [B_67,C_68,A_69] :
      ( k1_xboole_0 = B_67
      | v1_funct_2(C_68,A_69,B_67)
      | k1_relset_1(A_69,B_67,C_68) != A_69
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2396,plain,(
    ! [B_205,C_206,A_207] :
      ( k1_xboole_0 = B_205
      | v1_funct_2(C_206,A_207,B_205)
      | k1_relset_1(A_207,B_205,C_206) != A_207
      | ~ r1_tarski(k2_relat_1(C_206),B_205)
      | ~ r1_tarski(k1_relat_1(C_206),A_207)
      | ~ v1_relat_1(C_206) ) ),
    inference(resolution,[status(thm)],[c_24,c_361])).

tff(c_4828,plain,(
    ! [C_275,A_276] :
      ( k2_relat_1(C_275) = k1_xboole_0
      | v1_funct_2(C_275,A_276,k2_relat_1(C_275))
      | k1_relset_1(A_276,k2_relat_1(C_275),C_275) != A_276
      | ~ r1_tarski(k1_relat_1(C_275),A_276)
      | ~ v1_relat_1(C_275) ) ),
    inference(resolution,[status(thm)],[c_6,c_2396])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_91,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_4837,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4828,c_91])).

tff(c_4846,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_4837])).

tff(c_4847,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4846])).

tff(c_4850,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_4847])).

tff(c_4854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4850])).

tff(c_4855,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4846])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_853,plain,(
    ! [A_119,C_118] :
      ( k2_zfmisc_1(A_119,k2_relat_1(C_118)) = C_118
      | ~ r1_tarski(k2_zfmisc_1(A_119,k2_relat_1(C_118)),C_118)
      | ~ r1_tarski(k1_relat_1(C_118),A_119)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_838,c_2])).

tff(c_4872,plain,(
    ! [A_119] :
      ( k2_zfmisc_1(A_119,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_119,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_119)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4855,c_853])).

tff(c_4901,plain,(
    ! [A_119] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_12,c_12,c_4855,c_4872])).

tff(c_4918,plain,(
    ! [A_277] : ~ r1_tarski(k1_relat_1('#skF_1'),A_277) ),
    inference(splitLeft,[status(thm)],[c_4901])).

tff(c_4928,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_4918])).

tff(c_4929,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4901])).

tff(c_26,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_115,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_118,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_115])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118])).

tff(c_124,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_143,plain,(
    ! [A_37,C_38] :
      ( k1_relset_1(A_37,k1_xboole_0,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_166,plain,(
    ! [A_42] : k1_relset_1(A_42,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_124,c_143])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k1_relset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_171,plain,(
    ! [A_42] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_42,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_20])).

tff(c_178,plain,(
    ! [A_43] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_12,c_171])).

tff(c_192,plain,(
    ! [A_44] : r1_tarski(k1_relat_1(k1_xboole_0),A_44) ),
    inference(resolution,[status(thm)],[c_178,c_16])).

tff(c_92,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_199,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_192,c_101])).

tff(c_176,plain,(
    ! [A_42] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_12,c_171])).

tff(c_210,plain,(
    ! [A_45] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_176])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_217,plain,(
    ! [A_11,B_12] : k1_relset_1(A_11,B_12,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_210,c_22])).

tff(c_224,plain,(
    ! [A_11,B_12] : k1_relset_1(A_11,B_12,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_217])).

tff(c_202,plain,(
    ! [A_42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_176])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_495,plain,(
    ! [C_79,B_80] :
      ( v1_funct_2(C_79,k1_xboole_0,B_80)
      | k1_relset_1(k1_xboole_0,B_80,C_79) != k1_xboole_0
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_498,plain,(
    ! [B_80] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_80)
      | k1_relset_1(k1_xboole_0,B_80,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_202,c_495])).

tff(c_507,plain,(
    ! [B_80] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_498])).

tff(c_4984,plain,(
    ! [B_80] : v1_funct_2('#skF_1','#skF_1',B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_4929,c_507])).

tff(c_4995,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_4929,c_199])).

tff(c_4857,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4855,c_91])).

tff(c_4930,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_4857])).

tff(c_5315,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4995,c_4930])).

tff(c_5340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4984,c_5315])).

tff(c_5341,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5593,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5587,c_5341])).

tff(c_5607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_6,c_5593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.12  
% 5.87/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.13  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.87/2.13  
% 5.87/2.13  %Foreground sorts:
% 5.87/2.13  
% 5.87/2.13  
% 5.87/2.13  %Background operators:
% 5.87/2.13  
% 5.87/2.13  
% 5.87/2.13  %Foreground operators:
% 5.87/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.87/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.87/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.87/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.87/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.87/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.87/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.87/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.87/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.87/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.87/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.87/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.87/2.13  
% 5.87/2.14  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.87/2.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.87/2.14  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.87/2.14  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.87/2.14  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.87/2.14  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.87/2.14  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.87/2.14  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.87/2.14  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.87/2.14  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.87/2.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.87/2.14  tff(c_5587, plain, (![C_314, A_315, B_316]: (m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | ~r1_tarski(k2_relat_1(C_314), B_316) | ~r1_tarski(k1_relat_1(C_314), A_315) | ~v1_relat_1(C_314))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.87/2.14  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.87/2.14  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.14  tff(c_260, plain, (![C_51, A_52, B_53]: (m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~r1_tarski(k2_relat_1(C_51), B_53) | ~r1_tarski(k1_relat_1(C_51), A_52) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.87/2.14  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.87/2.14  tff(c_833, plain, (![C_115, A_116, B_117]: (r1_tarski(C_115, k2_zfmisc_1(A_116, B_117)) | ~r1_tarski(k2_relat_1(C_115), B_117) | ~r1_tarski(k1_relat_1(C_115), A_116) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_260, c_16])).
% 5.87/2.14  tff(c_838, plain, (![C_118, A_119]: (r1_tarski(C_118, k2_zfmisc_1(A_119, k2_relat_1(C_118))) | ~r1_tarski(k1_relat_1(C_118), A_119) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_6, c_833])).
% 5.87/2.14  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.87/2.14  tff(c_131, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.87/2.14  tff(c_142, plain, (![A_34, B_35, A_6]: (k1_relset_1(A_34, B_35, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_34, B_35)))), inference(resolution, [status(thm)], [c_18, c_131])).
% 5.87/2.14  tff(c_866, plain, (![A_121, C_122]: (k1_relset_1(A_121, k2_relat_1(C_122), C_122)=k1_relat_1(C_122) | ~r1_tarski(k1_relat_1(C_122), A_121) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_838, c_142])).
% 5.87/2.14  tff(c_881, plain, (![C_122]: (k1_relset_1(k1_relat_1(C_122), k2_relat_1(C_122), C_122)=k1_relat_1(C_122) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_6, c_866])).
% 5.87/2.14  tff(c_24, plain, (![C_16, A_14, B_15]: (m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~r1_tarski(k2_relat_1(C_16), B_15) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.87/2.14  tff(c_361, plain, (![B_67, C_68, A_69]: (k1_xboole_0=B_67 | v1_funct_2(C_68, A_69, B_67) | k1_relset_1(A_69, B_67, C_68)!=A_69 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_67))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.87/2.14  tff(c_2396, plain, (![B_205, C_206, A_207]: (k1_xboole_0=B_205 | v1_funct_2(C_206, A_207, B_205) | k1_relset_1(A_207, B_205, C_206)!=A_207 | ~r1_tarski(k2_relat_1(C_206), B_205) | ~r1_tarski(k1_relat_1(C_206), A_207) | ~v1_relat_1(C_206))), inference(resolution, [status(thm)], [c_24, c_361])).
% 5.87/2.14  tff(c_4828, plain, (![C_275, A_276]: (k2_relat_1(C_275)=k1_xboole_0 | v1_funct_2(C_275, A_276, k2_relat_1(C_275)) | k1_relset_1(A_276, k2_relat_1(C_275), C_275)!=A_276 | ~r1_tarski(k1_relat_1(C_275), A_276) | ~v1_relat_1(C_275))), inference(resolution, [status(thm)], [c_6, c_2396])).
% 5.87/2.14  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.87/2.14  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.87/2.14  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 5.87/2.14  tff(c_91, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 5.87/2.14  tff(c_4837, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4828, c_91])).
% 5.87/2.14  tff(c_4846, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_4837])).
% 5.87/2.14  tff(c_4847, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_4846])).
% 5.87/2.14  tff(c_4850, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_881, c_4847])).
% 5.87/2.14  tff(c_4854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_4850])).
% 5.87/2.14  tff(c_4855, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4846])).
% 5.87/2.14  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.87/2.14  tff(c_853, plain, (![A_119, C_118]: (k2_zfmisc_1(A_119, k2_relat_1(C_118))=C_118 | ~r1_tarski(k2_zfmisc_1(A_119, k2_relat_1(C_118)), C_118) | ~r1_tarski(k1_relat_1(C_118), A_119) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_838, c_2])).
% 5.87/2.14  tff(c_4872, plain, (![A_119]: (k2_zfmisc_1(A_119, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_119, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_119) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4855, c_853])).
% 5.87/2.14  tff(c_4901, plain, (![A_119]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_119))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_12, c_12, c_4855, c_4872])).
% 5.87/2.14  tff(c_4918, plain, (![A_277]: (~r1_tarski(k1_relat_1('#skF_1'), A_277))), inference(splitLeft, [status(thm)], [c_4901])).
% 5.87/2.14  tff(c_4928, plain, $false, inference(resolution, [status(thm)], [c_6, c_4918])).
% 5.87/2.14  tff(c_4929, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4901])).
% 5.87/2.14  tff(c_26, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.87/2.14  tff(c_47, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 5.87/2.14  tff(c_115, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_47])).
% 5.87/2.14  tff(c_118, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_115])).
% 5.87/2.14  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_118])).
% 5.87/2.14  tff(c_124, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_47])).
% 5.87/2.14  tff(c_143, plain, (![A_37, C_38]: (k1_relset_1(A_37, k1_xboole_0, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_131])).
% 5.87/2.14  tff(c_166, plain, (![A_42]: (k1_relset_1(A_42, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_124, c_143])).
% 5.87/2.14  tff(c_20, plain, (![A_8, B_9, C_10]: (m1_subset_1(k1_relset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.87/2.14  tff(c_171, plain, (![A_42]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_42)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_42, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_166, c_20])).
% 5.87/2.14  tff(c_178, plain, (![A_43]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_12, c_171])).
% 5.87/2.14  tff(c_192, plain, (![A_44]: (r1_tarski(k1_relat_1(k1_xboole_0), A_44))), inference(resolution, [status(thm)], [c_178, c_16])).
% 5.87/2.14  tff(c_92, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.87/2.14  tff(c_101, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_92])).
% 5.87/2.14  tff(c_199, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_192, c_101])).
% 5.87/2.14  tff(c_176, plain, (![A_42]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_12, c_171])).
% 5.87/2.14  tff(c_210, plain, (![A_45]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_176])).
% 5.87/2.14  tff(c_22, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.87/2.14  tff(c_217, plain, (![A_11, B_12]: (k1_relset_1(A_11, B_12, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_210, c_22])).
% 5.87/2.14  tff(c_224, plain, (![A_11, B_12]: (k1_relset_1(A_11, B_12, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_217])).
% 5.87/2.14  tff(c_202, plain, (![A_42]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_176])).
% 5.87/2.14  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.14  tff(c_30, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.87/2.14  tff(c_495, plain, (![C_79, B_80]: (v1_funct_2(C_79, k1_xboole_0, B_80) | k1_relset_1(k1_xboole_0, B_80, C_79)!=k1_xboole_0 | ~m1_subset_1(C_79, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 5.87/2.14  tff(c_498, plain, (![B_80]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_80) | k1_relset_1(k1_xboole_0, B_80, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_202, c_495])).
% 5.87/2.14  tff(c_507, plain, (![B_80]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_498])).
% 5.87/2.14  tff(c_4984, plain, (![B_80]: (v1_funct_2('#skF_1', '#skF_1', B_80))), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_4929, c_507])).
% 5.87/2.14  tff(c_4995, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_4929, c_199])).
% 5.87/2.14  tff(c_4857, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4855, c_91])).
% 5.87/2.14  tff(c_4930, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_4857])).
% 5.87/2.14  tff(c_5315, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4995, c_4930])).
% 5.87/2.14  tff(c_5340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4984, c_5315])).
% 5.87/2.14  tff(c_5341, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 5.87/2.14  tff(c_5593, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5587, c_5341])).
% 5.87/2.14  tff(c_5607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_6, c_5593])).
% 5.87/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.14  
% 5.87/2.14  Inference rules
% 5.87/2.14  ----------------------
% 5.87/2.14  #Ref     : 0
% 5.87/2.14  #Sup     : 1193
% 5.87/2.14  #Fact    : 0
% 5.87/2.14  #Define  : 0
% 5.87/2.14  #Split   : 5
% 5.87/2.14  #Chain   : 0
% 5.87/2.14  #Close   : 0
% 5.87/2.14  
% 5.87/2.14  Ordering : KBO
% 5.87/2.14  
% 5.87/2.14  Simplification rules
% 5.87/2.14  ----------------------
% 5.87/2.14  #Subsume      : 151
% 5.87/2.14  #Demod        : 2423
% 5.87/2.14  #Tautology    : 582
% 5.87/2.14  #SimpNegUnit  : 0
% 5.87/2.14  #BackRed      : 82
% 5.87/2.14  
% 5.87/2.14  #Partial instantiations: 0
% 5.87/2.14  #Strategies tried      : 1
% 5.87/2.14  
% 5.87/2.14  Timing (in seconds)
% 5.87/2.14  ----------------------
% 5.87/2.15  Preprocessing        : 0.30
% 5.87/2.15  Parsing              : 0.16
% 5.87/2.15  CNF conversion       : 0.02
% 5.87/2.15  Main loop            : 1.08
% 5.87/2.15  Inferencing          : 0.34
% 5.87/2.15  Reduction            : 0.38
% 5.87/2.15  Demodulation         : 0.30
% 5.87/2.15  BG Simplification    : 0.05
% 5.87/2.15  Subsumption          : 0.22
% 5.87/2.15  Abstraction          : 0.06
% 5.87/2.15  MUC search           : 0.00
% 5.87/2.15  Cooper               : 0.00
% 5.87/2.15  Total                : 1.42
% 5.87/2.15  Index Insertion      : 0.00
% 5.87/2.15  Index Deletion       : 0.00
% 5.87/2.15  Index Matching       : 0.00
% 5.87/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
