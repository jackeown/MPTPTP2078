%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:33 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 12.02s
% Verified   : 
% Statistics : Number of formulae       :  225 (108242 expanded)
%              Number of leaves         :   47 (38261 expanded)
%              Depth                    :   26
%              Number of atoms          :  541 (319317 expanded)
%              Number of equality atoms :  131 (87144 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_172,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_184,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_106,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_92,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_98,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_106,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_98])).

tff(c_88,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_105,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_98])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_128,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_105,c_82])).

tff(c_239,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_251,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_239])).

tff(c_80,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_123,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_105,c_80])).

tff(c_257,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_123])).

tff(c_84,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_107,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_84])).

tff(c_116,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_107])).

tff(c_267,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_116])).

tff(c_225,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_237,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_225])).

tff(c_263,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_237])).

tff(c_266,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_128])).

tff(c_892,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_909,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4') = k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_266,c_892])).

tff(c_924,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_263,c_909])).

tff(c_981,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_924])).

tff(c_988,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_267])).

tff(c_986,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_266])).

tff(c_262,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_251])).

tff(c_984,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_262])).

tff(c_78,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1375,plain,(
    ! [A_176,B_177,C_178] :
      ( k2_tops_2(A_176,B_177,C_178) = k2_funct_1(C_178)
      | ~ v2_funct_1(C_178)
      | k2_relset_1(A_176,B_177,C_178) != B_177
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_2(C_178,A_176,B_177)
      | ~ v1_funct_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1381,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_986,c_1375])).

tff(c_1406,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_988,c_984,c_78,c_1381])).

tff(c_70,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k2_tops_2(A_39,B_40,C_41),k1_zfmisc_1(k2_zfmisc_1(B_40,A_39)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1425,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_70])).

tff(c_1429,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_988,c_986,c_1425])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1489,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1429,c_2])).

tff(c_134,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_134])).

tff(c_1212,plain,(
    ! [C_159,A_160,B_161] :
      ( v1_funct_1(k2_funct_1(C_159))
      | k2_relset_1(A_160,B_161,C_159) != B_161
      | ~ v2_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_2(C_159,A_160,B_161)
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1218,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_986,c_1212])).

tff(c_1243,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_988,c_78,c_984,c_1218])).

tff(c_1329,plain,(
    ! [C_171,B_172,A_173] :
      ( v1_funct_2(k2_funct_1(C_171),B_172,A_173)
      | k2_relset_1(A_173,B_172,C_171) != B_172
      | ~ v2_funct_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172)))
      | ~ v1_funct_2(C_171,A_173,B_172)
      | ~ v1_funct_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1335,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_986,c_1329])).

tff(c_1360,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_988,c_78,c_984,c_1335])).

tff(c_6,plain,(
    ! [A_3] :
      ( v2_funct_1(k2_funct_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1486,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1429,c_24])).

tff(c_56,plain,(
    ! [C_30,A_28,B_29] :
      ( v1_funct_1(k2_funct_1(C_30))
      | k2_relset_1(A_28,B_29,C_30) != B_29
      | ~ v2_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1439,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1429,c_56])).

tff(c_1473,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_1360,c_1439])).

tff(c_6018,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1473])).

tff(c_6019,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6018])).

tff(c_6022,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_6019])).

tff(c_6026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_6022])).

tff(c_6028,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6018])).

tff(c_12,plain,(
    ! [A_4] :
      ( k2_relat_1(k2_funct_1(A_4)) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6027,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_6018])).

tff(c_6029,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6027])).

tff(c_6032,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6029])).

tff(c_6036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_6032])).

tff(c_6038,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6027])).

tff(c_6054,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6038,c_1486])).

tff(c_6037,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_6027])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1370,plain,(
    ! [A_1,B_172,A_173] :
      ( v1_funct_2(k2_funct_1(A_1),B_172,A_173)
      | k2_relset_1(A_173,B_172,A_1) != B_172
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_2(A_1,A_173,B_172)
      | ~ v1_funct_1(A_1)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_173,B_172)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1329])).

tff(c_354,plain,(
    ! [A_97,B_98,C_99] :
      ( m1_subset_1(k2_relset_1(A_97,B_98,C_99),k1_zfmisc_1(B_98))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_379,plain,(
    ! [A_97,B_98,C_99] :
      ( r1_tarski(k2_relset_1(A_97,B_98,C_99),B_98)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(resolution,[status(thm)],[c_354,c_2])).

tff(c_1474,plain,(
    r1_tarski(k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1429,c_379])).

tff(c_1577,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1474])).

tff(c_1594,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1577])).

tff(c_1596,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_86,c_78,c_1594])).

tff(c_18,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1488,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1429,c_18])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1487,plain,(
    k1_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1429,c_22])).

tff(c_36,plain,(
    ! [B_19,A_18,C_20] :
      ( k1_xboole_0 = B_19
      | k1_relset_1(A_18,B_19,C_20) = A_18
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1446,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1429,c_36])).

tff(c_1480,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1446])).

tff(c_1696,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1480])).

tff(c_1697,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1696])).

tff(c_58,plain,(
    ! [B_32,A_31] :
      ( m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32),A_31)))
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1702,plain,(
    ! [A_31] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),A_31)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_31)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_58])).

tff(c_1715,plain,(
    ! [A_31] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),A_31)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1243,c_1702])).

tff(c_6290,plain,(
    ! [A_372] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),A_372)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6038,c_1715])).

tff(c_16,plain,(
    ! [A_5] :
      ( k2_funct_1(k2_funct_1(A_5)) = A_5
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [C_30,B_29,A_28] :
      ( m1_subset_1(k2_funct_1(C_30),k1_zfmisc_1(k2_zfmisc_1(B_29,A_28)))
      | k2_relset_1(A_28,B_29,C_30) != B_29
      | ~ v2_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1613,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( r2_funct_2(A_182,B_183,C_184,C_184)
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(D_185,A_182,B_183)
      | ~ v1_funct_1(D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(C_184,A_182,B_183)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1621,plain,(
    ! [C_184] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),C_184,C_184)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_184,k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(C_184) ) ),
    inference(resolution,[status(thm)],[c_986,c_1613])).

tff(c_1657,plain,(
    ! [C_186] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),C_186,C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_186,k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(C_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_988,c_1621])).

tff(c_2493,plain,(
    ! [C_220] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(C_220),k2_funct_1(C_220))
      | ~ v1_funct_2(k2_funct_1(C_220),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(C_220))
      | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),C_220) != k1_relat_1('#skF_4')
      | ~ v2_funct_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_220,k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(C_220) ) ),
    inference(resolution,[status(thm)],[c_52,c_1657])).

tff(c_2496,plain,(
    ! [A_5] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),A_5,k2_funct_1(k2_funct_1(A_5)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(A_5)),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_5)))
      | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1(A_5)) != k1_relat_1('#skF_4')
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ m1_subset_1(k2_funct_1(A_5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(k2_funct_1(A_5),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2493])).

tff(c_6293,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4',k2_funct_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6290,c_2496])).

tff(c_6350,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4',k2_funct_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1596,c_142,c_86,c_78,c_1243,c_1360,c_6028,c_6054,c_6037,c_6293])).

tff(c_7707,plain,(
    ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6350])).

tff(c_7710,plain,
    ( k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1370,c_7707])).

tff(c_7720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_1243,c_1360,c_6028,c_6054,c_7710])).

tff(c_7722,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6350])).

tff(c_4497,plain,(
    ! [A_312] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1(A_312)),A_312)
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(A_312)),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_312)))
      | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1(A_312)) != k1_relat_1('#skF_4')
      | ~ v2_funct_1(k2_funct_1(A_312))
      | ~ m1_subset_1(k2_funct_1(A_312),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(k2_funct_1(A_312),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(A_312))
      | ~ v2_funct_1(A_312)
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2493])).

tff(c_4518,plain,(
    ! [A_312] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1(A_312)),A_312)
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(A_312)),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_312)))
      | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1(A_312)) != k1_relat_1('#skF_4')
      | ~ v2_funct_1(k2_funct_1(A_312))
      | ~ v1_funct_2(k2_funct_1(A_312),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(A_312))
      | ~ v2_funct_1(A_312)
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312)
      | ~ r1_tarski(k2_funct_1(A_312),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_4497])).

tff(c_7734,plain,(
    ! [A_441,B_442,A_443] :
      ( k2_tops_2(A_441,B_442,A_443) = k2_funct_1(A_443)
      | ~ v2_funct_1(A_443)
      | k2_relset_1(A_441,B_442,A_443) != B_442
      | ~ v1_funct_2(A_443,A_441,B_442)
      | ~ v1_funct_1(A_443)
      | ~ r1_tarski(A_443,k2_zfmisc_1(A_441,B_442)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1375])).

tff(c_7794,plain,
    ( k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1489,c_7734])).

tff(c_7840,plain,(
    k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_1360,c_6054,c_6028,c_7794])).

tff(c_76,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_133,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_106,c_106,c_105,c_105,c_105,c_76])).

tff(c_265,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_257,c_257,c_133])).

tff(c_983,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_981,c_981,c_265])).

tff(c_1418,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_983])).

tff(c_7855,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7840,c_1418])).

tff(c_7891,plain,
    ( ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_4518,c_7855])).

tff(c_7898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_142,c_86,c_78,c_1243,c_1360,c_6028,c_6054,c_6037,c_7722,c_7891])).

tff(c_7899,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_924])).

tff(c_7909,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7899,c_267])).

tff(c_7907,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7899,c_266])).

tff(c_28,plain,(
    ! [C_20,A_18] :
      ( k1_xboole_0 = C_20
      | ~ v1_funct_2(C_20,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7990,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k1_xboole_0)
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7907,c_28])).

tff(c_8018,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7909,c_7990])).

tff(c_8026,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8018])).

tff(c_7900,plain,(
    k2_struct_0('#skF_2') != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_924])).

tff(c_8032,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8026,c_7900])).

tff(c_8031,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8026,c_7909])).

tff(c_8027,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8026,c_7907])).

tff(c_64,plain,(
    ! [A_33,B_34] :
      ( k1_relset_1(A_33,A_33,B_34) = A_33
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_8125,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8027,c_64])).

tff(c_8162,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8031,c_8125])).

tff(c_132,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_264,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_132])).

tff(c_7908,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_struct_0('#skF_2'),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7899,c_264])).

tff(c_8028,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8026,c_7908])).

tff(c_238,plain,(
    ! [A_79,B_80,A_1] :
      ( k1_relset_1(A_79,B_80,A_1) = k1_relat_1(A_1)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_8103,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8028,c_238])).

tff(c_8190,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8162,c_8103])).

tff(c_8191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8032,c_8190])).

tff(c_8192,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8018])).

tff(c_8193,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8018])).

tff(c_8286,plain,(
    k2_struct_0('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8192,c_8193])).

tff(c_8250,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8192,c_7909])).

tff(c_38,plain,(
    ! [A_21,B_22] : v1_funct_2('#skF_1'(A_21,B_22),A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    ! [A_21,B_22] : m1_subset_1('#skF_1'(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_388,plain,(
    ! [C_100,A_101] :
      ( k1_xboole_0 = C_100
      | ~ v1_funct_2(C_100,A_101,k1_xboole_0)
      | k1_xboole_0 = A_101
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_396,plain,(
    ! [A_21] :
      ( '#skF_1'(A_21,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2('#skF_1'(A_21,k1_xboole_0),A_21,k1_xboole_0)
      | k1_xboole_0 = A_21 ) ),
    inference(resolution,[status(thm)],[c_48,c_388])).

tff(c_407,plain,(
    ! [A_102] :
      ( '#skF_1'(A_102,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 = A_102 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_396])).

tff(c_422,plain,(
    ! [A_102] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_102,k1_xboole_0)))
      | k1_xboole_0 = A_102 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_48])).

tff(c_8265,plain,(
    ! [A_102] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_102,'#skF_4')))
      | A_102 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8192,c_8192,c_8192,c_422])).

tff(c_8246,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8192,c_7907])).

tff(c_8844,plain,(
    ! [A_477,B_478,C_479,D_480] :
      ( r2_funct_2(A_477,B_478,C_479,C_479)
      | ~ m1_subset_1(D_480,k1_zfmisc_1(k2_zfmisc_1(A_477,B_478)))
      | ~ v1_funct_2(D_480,A_477,B_478)
      | ~ v1_funct_1(D_480)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(A_477,B_478)))
      | ~ v1_funct_2(C_479,A_477,B_478)
      | ~ v1_funct_1(C_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8852,plain,(
    ! [C_479] :
      ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',C_479,C_479)
      | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4')))
      | ~ v1_funct_2(C_479,k2_struct_0('#skF_2'),'#skF_4')
      | ~ v1_funct_1(C_479) ) ),
    inference(resolution,[status(thm)],[c_8246,c_8844])).

tff(c_8994,plain,(
    ! [C_488] :
      ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',C_488,C_488)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4')))
      | ~ v1_funct_2(C_488,k2_struct_0('#skF_2'),'#skF_4')
      | ~ v1_funct_1(C_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8250,c_8852])).

tff(c_8997,plain,
    ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8265,c_8994])).

tff(c_9020,plain,
    ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4')
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8250,c_8997])).

tff(c_9021,plain,(
    r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_8286,c_9020])).

tff(c_7905,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7899,c_7899,c_262])).

tff(c_8248,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8192,c_8192,c_7905])).

tff(c_8489,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8246,c_56])).

tff(c_8512,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8250,c_78,c_8248,c_8489])).

tff(c_54,plain,(
    ! [C_30,B_29,A_28] :
      ( v1_funct_2(k2_funct_1(C_30),B_29,A_28)
      | k2_relset_1(A_28,B_29,C_30) != B_29
      | ~ v2_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8486,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2'))
    | k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8246,c_54])).

tff(c_8509,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8250,c_78,c_8248,c_8486])).

tff(c_8529,plain,(
    ! [A_464,B_465,C_466] :
      ( k2_tops_2(A_464,B_465,C_466) = k2_funct_1(C_466)
      | ~ v2_funct_1(C_466)
      | k2_relset_1(A_464,B_465,C_466) != B_465
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465)))
      | ~ v1_funct_2(C_466,A_464,B_465)
      | ~ v1_funct_1(C_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_8532,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') != '#skF_4'
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8246,c_8529])).

tff(c_8556,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8250,c_8248,c_78,c_8532])).

tff(c_8636,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8556,c_70])).

tff(c_8642,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8250,c_8246,c_8636])).

tff(c_72,plain,(
    ! [A_39,B_40,C_41] :
      ( v1_funct_2(k2_tops_2(A_39,B_40,C_41),B_40,A_39)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_8809,plain,
    ( v1_funct_2(k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')),k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8642,c_72])).

tff(c_8836,plain,(
    v1_funct_2(k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')),k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8512,c_8509,c_8809])).

tff(c_8194,plain,(
    ! [A_450,B_451,C_452] :
      ( m1_subset_1(k2_tops_2(A_450,B_451,C_452),k1_zfmisc_1(k2_zfmisc_1(B_451,A_450)))
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451)))
      | ~ v1_funct_2(C_452,A_450,B_451)
      | ~ v1_funct_1(C_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_8241,plain,(
    ! [B_451,C_452] :
      ( k2_tops_2(k1_xboole_0,B_451,C_452) = k1_xboole_0
      | ~ v1_funct_2(k2_tops_2(k1_xboole_0,B_451,C_452),B_451,k1_xboole_0)
      | k1_xboole_0 = B_451
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_451)))
      | ~ v1_funct_2(C_452,k1_xboole_0,B_451)
      | ~ v1_funct_1(C_452) ) ),
    inference(resolution,[status(thm)],[c_8194,c_28])).

tff(c_19100,plain,(
    ! [B_795,C_796] :
      ( k2_tops_2('#skF_4',B_795,C_796) = '#skF_4'
      | ~ v1_funct_2(k2_tops_2('#skF_4',B_795,C_796),B_795,'#skF_4')
      | B_795 = '#skF_4'
      | ~ m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_795)))
      | ~ v1_funct_2(C_796,'#skF_4',B_795)
      | ~ v1_funct_1(C_796) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8192,c_8192,c_8192,c_8192,c_8192,c_8192,c_8192,c_8241])).

tff(c_19107,plain,
    ( k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')) = '#skF_4'
    | k2_struct_0('#skF_2') = '#skF_4'
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8836,c_19100])).

tff(c_19120,plain,
    ( k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')) = '#skF_4'
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8512,c_8509,c_8642,c_19107])).

tff(c_19121,plain,(
    k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_8286,c_19120])).

tff(c_7904,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_xboole_0,'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7899,c_7899,c_7899,c_265])).

tff(c_8287,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8192,c_8192,c_8192,c_7904])).

tff(c_8627,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8287])).

tff(c_19199,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19121,c_8627])).

tff(c_19205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9021,c_19199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.71/4.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.71/4.56  
% 11.71/4.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.71/4.56  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.71/4.56  
% 11.71/4.56  %Foreground sorts:
% 11.71/4.56  
% 11.71/4.56  
% 11.71/4.56  %Background operators:
% 11.71/4.56  
% 11.71/4.56  
% 11.71/4.56  %Foreground operators:
% 11.71/4.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.71/4.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.71/4.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.71/4.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.71/4.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.71/4.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.71/4.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.71/4.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.71/4.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.71/4.56  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 11.71/4.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.71/4.56  tff('#skF_2', type, '#skF_2': $i).
% 11.71/4.56  tff('#skF_3', type, '#skF_3': $i).
% 11.71/4.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.71/4.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.71/4.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.71/4.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.71/4.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.71/4.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.71/4.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.71/4.56  tff('#skF_4', type, '#skF_4': $i).
% 11.71/4.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.71/4.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.71/4.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.71/4.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.71/4.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.71/4.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.71/4.56  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 11.71/4.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.71/4.56  
% 12.02/4.59  tff(f_206, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 12.02/4.59  tff(f_160, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 12.02/4.59  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.02/4.59  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.02/4.59  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.02/4.59  tff(f_172, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 12.02/4.59  tff(f_184, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 12.02/4.59  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.02/4.59  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.02/4.59  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 12.02/4.59  tff(f_41, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 12.02/4.59  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.02/4.59  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 12.02/4.59  tff(f_148, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 12.02/4.59  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 12.02/4.59  tff(f_120, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 12.02/4.59  tff(f_156, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 12.02/4.59  tff(f_106, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 12.02/4.59  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.59  tff(c_92, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.59  tff(c_98, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_160])).
% 12.02/4.59  tff(c_106, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_92, c_98])).
% 12.02/4.59  tff(c_88, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.59  tff(c_105, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_88, c_98])).
% 12.02/4.59  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.59  tff(c_128, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_105, c_82])).
% 12.02/4.59  tff(c_239, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.02/4.59  tff(c_251, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_239])).
% 12.02/4.59  tff(c_80, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.59  tff(c_123, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_105, c_80])).
% 12.02/4.59  tff(c_257, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_123])).
% 12.02/4.59  tff(c_84, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.59  tff(c_107, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_84])).
% 12.02/4.59  tff(c_116, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_107])).
% 12.02/4.59  tff(c_267, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_116])).
% 12.02/4.59  tff(c_225, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.02/4.59  tff(c_237, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_225])).
% 12.02/4.59  tff(c_263, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_237])).
% 12.02/4.59  tff(c_266, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_128])).
% 12.02/4.59  tff(c_892, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.02/4.60  tff(c_909, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_266, c_892])).
% 12.02/4.60  tff(c_924, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_263, c_909])).
% 12.02/4.60  tff(c_981, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_924])).
% 12.02/4.60  tff(c_988, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_267])).
% 12.02/4.60  tff(c_986, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_266])).
% 12.02/4.60  tff(c_262, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_251])).
% 12.02/4.60  tff(c_984, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_262])).
% 12.02/4.60  tff(c_78, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.60  tff(c_1375, plain, (![A_176, B_177, C_178]: (k2_tops_2(A_176, B_177, C_178)=k2_funct_1(C_178) | ~v2_funct_1(C_178) | k2_relset_1(A_176, B_177, C_178)!=B_177 | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_2(C_178, A_176, B_177) | ~v1_funct_1(C_178))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.02/4.60  tff(c_1381, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_986, c_1375])).
% 12.02/4.60  tff(c_1406, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_988, c_984, c_78, c_1381])).
% 12.02/4.60  tff(c_70, plain, (![A_39, B_40, C_41]: (m1_subset_1(k2_tops_2(A_39, B_40, C_41), k1_zfmisc_1(k2_zfmisc_1(B_40, A_39))) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.02/4.60  tff(c_1425, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1406, c_70])).
% 12.02/4.60  tff(c_1429, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_988, c_986, c_1425])).
% 12.02/4.60  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.02/4.60  tff(c_1489, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_1429, c_2])).
% 12.02/4.60  tff(c_134, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.02/4.60  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_134])).
% 12.02/4.60  tff(c_1212, plain, (![C_159, A_160, B_161]: (v1_funct_1(k2_funct_1(C_159)) | k2_relset_1(A_160, B_161, C_159)!=B_161 | ~v2_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_2(C_159, A_160, B_161) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.02/4.60  tff(c_1218, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_986, c_1212])).
% 12.02/4.60  tff(c_1243, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_988, c_78, c_984, c_1218])).
% 12.02/4.60  tff(c_1329, plain, (![C_171, B_172, A_173]: (v1_funct_2(k2_funct_1(C_171), B_172, A_173) | k2_relset_1(A_173, B_172, C_171)!=B_172 | ~v2_funct_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))) | ~v1_funct_2(C_171, A_173, B_172) | ~v1_funct_1(C_171))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.02/4.60  tff(c_1335, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_986, c_1329])).
% 12.02/4.60  tff(c_1360, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_988, c_78, c_984, c_1335])).
% 12.02/4.60  tff(c_6, plain, (![A_3]: (v2_funct_1(k2_funct_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.02/4.60  tff(c_24, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.02/4.60  tff(c_1486, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1429, c_24])).
% 12.02/4.60  tff(c_56, plain, (![C_30, A_28, B_29]: (v1_funct_1(k2_funct_1(C_30)) | k2_relset_1(A_28, B_29, C_30)!=B_29 | ~v2_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.02/4.60  tff(c_1439, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1429, c_56])).
% 12.02/4.60  tff(c_1473, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_1360, c_1439])).
% 12.02/4.60  tff(c_6018, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1473])).
% 12.02/4.60  tff(c_6019, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6018])).
% 12.02/4.60  tff(c_6022, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_6019])).
% 12.02/4.60  tff(c_6026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_6022])).
% 12.02/4.60  tff(c_6028, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6018])).
% 12.02/4.60  tff(c_12, plain, (![A_4]: (k2_relat_1(k2_funct_1(A_4))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.02/4.60  tff(c_6027, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_6018])).
% 12.02/4.60  tff(c_6029, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_6027])).
% 12.02/4.60  tff(c_6032, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_6029])).
% 12.02/4.60  tff(c_6036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_6032])).
% 12.02/4.60  tff(c_6038, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_6027])).
% 12.02/4.60  tff(c_6054, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6038, c_1486])).
% 12.02/4.60  tff(c_6037, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_6027])).
% 12.02/4.60  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.02/4.60  tff(c_1370, plain, (![A_1, B_172, A_173]: (v1_funct_2(k2_funct_1(A_1), B_172, A_173) | k2_relset_1(A_173, B_172, A_1)!=B_172 | ~v2_funct_1(A_1) | ~v1_funct_2(A_1, A_173, B_172) | ~v1_funct_1(A_1) | ~r1_tarski(A_1, k2_zfmisc_1(A_173, B_172)))), inference(resolution, [status(thm)], [c_4, c_1329])).
% 12.02/4.60  tff(c_354, plain, (![A_97, B_98, C_99]: (m1_subset_1(k2_relset_1(A_97, B_98, C_99), k1_zfmisc_1(B_98)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.02/4.60  tff(c_379, plain, (![A_97, B_98, C_99]: (r1_tarski(k2_relset_1(A_97, B_98, C_99), B_98) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(resolution, [status(thm)], [c_354, c_2])).
% 12.02/4.60  tff(c_1474, plain, (r1_tarski(k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1429, c_379])).
% 12.02/4.60  tff(c_1577, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1474])).
% 12.02/4.60  tff(c_1594, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_1577])).
% 12.02/4.60  tff(c_1596, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_86, c_78, c_1594])).
% 12.02/4.60  tff(c_18, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.02/4.60  tff(c_1488, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1429, c_18])).
% 12.02/4.60  tff(c_22, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.02/4.60  tff(c_1487, plain, (k1_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1429, c_22])).
% 12.02/4.60  tff(c_36, plain, (![B_19, A_18, C_20]: (k1_xboole_0=B_19 | k1_relset_1(A_18, B_19, C_20)=A_18 | ~v1_funct_2(C_20, A_18, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.02/4.60  tff(c_1446, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1429, c_36])).
% 12.02/4.60  tff(c_1480, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1446])).
% 12.02/4.60  tff(c_1696, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1480])).
% 12.02/4.60  tff(c_1697, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1696])).
% 12.02/4.60  tff(c_58, plain, (![B_32, A_31]: (m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32), A_31))) | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.02/4.60  tff(c_1702, plain, (![A_31]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), A_31))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_31) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1697, c_58])).
% 12.02/4.60  tff(c_1715, plain, (![A_31]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), A_31))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_31))), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1243, c_1702])).
% 12.02/4.60  tff(c_6290, plain, (![A_372]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), A_372))) | ~r1_tarski(k1_relat_1('#skF_4'), A_372))), inference(demodulation, [status(thm), theory('equality')], [c_6038, c_1715])).
% 12.02/4.60  tff(c_16, plain, (![A_5]: (k2_funct_1(k2_funct_1(A_5))=A_5 | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.02/4.60  tff(c_52, plain, (![C_30, B_29, A_28]: (m1_subset_1(k2_funct_1(C_30), k1_zfmisc_1(k2_zfmisc_1(B_29, A_28))) | k2_relset_1(A_28, B_29, C_30)!=B_29 | ~v2_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.02/4.60  tff(c_1613, plain, (![A_182, B_183, C_184, D_185]: (r2_funct_2(A_182, B_183, C_184, C_184) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(D_185, A_182, B_183) | ~v1_funct_1(D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(C_184, A_182, B_183) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.02/4.60  tff(c_1621, plain, (![C_184]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), C_184, C_184) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2(C_184, k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(C_184))), inference(resolution, [status(thm)], [c_986, c_1613])).
% 12.02/4.60  tff(c_1657, plain, (![C_186]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), C_186, C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2(C_186, k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(C_186))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_988, c_1621])).
% 12.02/4.60  tff(c_2493, plain, (![C_220]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(C_220), k2_funct_1(C_220)) | ~v1_funct_2(k2_funct_1(C_220), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(C_220)) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), C_220)!=k1_relat_1('#skF_4') | ~v2_funct_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~v1_funct_2(C_220, k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(C_220))), inference(resolution, [status(thm)], [c_52, c_1657])).
% 12.02/4.60  tff(c_2496, plain, (![A_5]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), A_5, k2_funct_1(k2_funct_1(A_5))) | ~v1_funct_2(k2_funct_1(k2_funct_1(A_5)), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_5))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1(A_5))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1(A_5)) | ~m1_subset_1(k2_funct_1(A_5), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~v1_funct_2(k2_funct_1(A_5), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2493])).
% 12.02/4.60  tff(c_6293, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6290, c_2496])).
% 12.02/4.60  tff(c_6350, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1596, c_142, c_86, c_78, c_1243, c_1360, c_6028, c_6054, c_6037, c_6293])).
% 12.02/4.60  tff(c_7707, plain, (~v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6350])).
% 12.02/4.60  tff(c_7710, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_1370, c_7707])).
% 12.02/4.60  tff(c_7720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1489, c_1243, c_1360, c_6028, c_6054, c_7710])).
% 12.02/4.60  tff(c_7722, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6350])).
% 12.02/4.60  tff(c_4497, plain, (![A_312]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1(A_312)), A_312) | ~v1_funct_2(k2_funct_1(k2_funct_1(A_312)), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_312))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1(A_312))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1(A_312)) | ~m1_subset_1(k2_funct_1(A_312), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~v1_funct_2(k2_funct_1(A_312), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(A_312)) | ~v2_funct_1(A_312) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2493])).
% 12.02/4.60  tff(c_4518, plain, (![A_312]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1(A_312)), A_312) | ~v1_funct_2(k2_funct_1(k2_funct_1(A_312)), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_312))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1(A_312))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1(A_312)) | ~v1_funct_2(k2_funct_1(A_312), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(A_312)) | ~v2_funct_1(A_312) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312) | ~r1_tarski(k2_funct_1(A_312), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))))), inference(resolution, [status(thm)], [c_4, c_4497])).
% 12.02/4.60  tff(c_7734, plain, (![A_441, B_442, A_443]: (k2_tops_2(A_441, B_442, A_443)=k2_funct_1(A_443) | ~v2_funct_1(A_443) | k2_relset_1(A_441, B_442, A_443)!=B_442 | ~v1_funct_2(A_443, A_441, B_442) | ~v1_funct_1(A_443) | ~r1_tarski(A_443, k2_zfmisc_1(A_441, B_442)))), inference(resolution, [status(thm)], [c_4, c_1375])).
% 12.02/4.60  tff(c_7794, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1489, c_7734])).
% 12.02/4.60  tff(c_7840, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_1360, c_6054, c_6028, c_7794])).
% 12.02/4.60  tff(c_76, plain, (~r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 12.02/4.60  tff(c_133, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_106, c_106, c_105, c_105, c_105, c_76])).
% 12.02/4.60  tff(c_265, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_257, c_257, c_133])).
% 12.02/4.60  tff(c_983, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_981, c_981, c_265])).
% 12.02/4.60  tff(c_1418, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_983])).
% 12.02/4.60  tff(c_7855, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7840, c_1418])).
% 12.02/4.60  tff(c_7891, plain, (~v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_4518, c_7855])).
% 12.02/4.60  tff(c_7898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1489, c_142, c_86, c_78, c_1243, c_1360, c_6028, c_6054, c_6037, c_7722, c_7891])).
% 12.02/4.60  tff(c_7899, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_924])).
% 12.02/4.60  tff(c_7909, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7899, c_267])).
% 12.02/4.60  tff(c_7907, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_7899, c_266])).
% 12.02/4.60  tff(c_28, plain, (![C_20, A_18]: (k1_xboole_0=C_20 | ~v1_funct_2(C_20, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.02/4.60  tff(c_7990, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k1_xboole_0) | k2_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_7907, c_28])).
% 12.02/4.60  tff(c_8018, plain, (k1_xboole_0='#skF_4' | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7909, c_7990])).
% 12.02/4.60  tff(c_8026, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8018])).
% 12.02/4.60  tff(c_7900, plain, (k2_struct_0('#skF_2')!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_924])).
% 12.02/4.60  tff(c_8032, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8026, c_7900])).
% 12.02/4.60  tff(c_8031, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8026, c_7909])).
% 12.02/4.60  tff(c_8027, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8026, c_7907])).
% 12.02/4.60  tff(c_64, plain, (![A_33, B_34]: (k1_relset_1(A_33, A_33, B_34)=A_33 | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_156])).
% 12.02/4.60  tff(c_8125, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8027, c_64])).
% 12.02/4.60  tff(c_8162, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8031, c_8125])).
% 12.02/4.60  tff(c_132, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_128, c_2])).
% 12.02/4.60  tff(c_264, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_132])).
% 12.02/4.60  tff(c_7908, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_struct_0('#skF_2'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_7899, c_264])).
% 12.02/4.60  tff(c_8028, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8026, c_7908])).
% 12.02/4.60  tff(c_238, plain, (![A_79, B_80, A_1]: (k1_relset_1(A_79, B_80, A_1)=k1_relat_1(A_1) | ~r1_tarski(A_1, k2_zfmisc_1(A_79, B_80)))), inference(resolution, [status(thm)], [c_4, c_225])).
% 12.02/4.60  tff(c_8103, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8028, c_238])).
% 12.02/4.60  tff(c_8190, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8162, c_8103])).
% 12.02/4.60  tff(c_8191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8032, c_8190])).
% 12.02/4.60  tff(c_8192, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8018])).
% 12.02/4.60  tff(c_8193, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8018])).
% 12.02/4.60  tff(c_8286, plain, (k2_struct_0('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8192, c_8193])).
% 12.02/4.60  tff(c_8250, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8192, c_7909])).
% 12.02/4.60  tff(c_38, plain, (![A_21, B_22]: (v1_funct_2('#skF_1'(A_21, B_22), A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.02/4.60  tff(c_48, plain, (![A_21, B_22]: (m1_subset_1('#skF_1'(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.02/4.60  tff(c_388, plain, (![C_100, A_101]: (k1_xboole_0=C_100 | ~v1_funct_2(C_100, A_101, k1_xboole_0) | k1_xboole_0=A_101 | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.02/4.60  tff(c_396, plain, (![A_21]: ('#skF_1'(A_21, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2('#skF_1'(A_21, k1_xboole_0), A_21, k1_xboole_0) | k1_xboole_0=A_21)), inference(resolution, [status(thm)], [c_48, c_388])).
% 12.02/4.60  tff(c_407, plain, (![A_102]: ('#skF_1'(A_102, k1_xboole_0)=k1_xboole_0 | k1_xboole_0=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_396])).
% 12.02/4.60  tff(c_422, plain, (![A_102]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_102, k1_xboole_0))) | k1_xboole_0=A_102)), inference(superposition, [status(thm), theory('equality')], [c_407, c_48])).
% 12.02/4.60  tff(c_8265, plain, (![A_102]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_102, '#skF_4'))) | A_102='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8192, c_8192, c_8192, c_422])).
% 12.02/4.60  tff(c_8246, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8192, c_7907])).
% 12.02/4.60  tff(c_8844, plain, (![A_477, B_478, C_479, D_480]: (r2_funct_2(A_477, B_478, C_479, C_479) | ~m1_subset_1(D_480, k1_zfmisc_1(k2_zfmisc_1(A_477, B_478))) | ~v1_funct_2(D_480, A_477, B_478) | ~v1_funct_1(D_480) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(A_477, B_478))) | ~v1_funct_2(C_479, A_477, B_478) | ~v1_funct_1(C_479))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.02/4.60  tff(c_8852, plain, (![C_479]: (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', C_479, C_479) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2(C_479, k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1(C_479))), inference(resolution, [status(thm)], [c_8246, c_8844])).
% 12.02/4.60  tff(c_8994, plain, (![C_488]: (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', C_488, C_488) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2(C_488, k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1(C_488))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8250, c_8852])).
% 12.02/4.60  tff(c_8997, plain, (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4') | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_8265, c_8994])).
% 12.02/4.60  tff(c_9020, plain, (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4') | k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8250, c_8997])).
% 12.02/4.60  tff(c_9021, plain, (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_8286, c_9020])).
% 12.02/4.60  tff(c_7905, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7899, c_7899, c_262])).
% 12.02/4.60  tff(c_8248, plain, (k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8192, c_8192, c_7905])).
% 12.02/4.60  tff(c_8489, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8246, c_56])).
% 12.02/4.60  tff(c_8512, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8250, c_78, c_8248, c_8489])).
% 12.02/4.60  tff(c_54, plain, (![C_30, B_29, A_28]: (v1_funct_2(k2_funct_1(C_30), B_29, A_28) | k2_relset_1(A_28, B_29, C_30)!=B_29 | ~v2_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.02/4.60  tff(c_8486, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2')) | k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8246, c_54])).
% 12.02/4.60  tff(c_8509, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8250, c_78, c_8248, c_8486])).
% 12.02/4.60  tff(c_8529, plain, (![A_464, B_465, C_466]: (k2_tops_2(A_464, B_465, C_466)=k2_funct_1(C_466) | ~v2_funct_1(C_466) | k2_relset_1(A_464, B_465, C_466)!=B_465 | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))) | ~v1_funct_2(C_466, A_464, B_465) | ~v1_funct_1(C_466))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.02/4.60  tff(c_8532, plain, (k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')!='#skF_4' | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8246, c_8529])).
% 12.02/4.60  tff(c_8556, plain, (k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8250, c_8248, c_78, c_8532])).
% 12.02/4.60  tff(c_8636, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8556, c_70])).
% 12.02/4.60  tff(c_8642, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8250, c_8246, c_8636])).
% 12.02/4.60  tff(c_72, plain, (![A_39, B_40, C_41]: (v1_funct_2(k2_tops_2(A_39, B_40, C_41), B_40, A_39) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.02/4.60  tff(c_8809, plain, (v1_funct_2(k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4')), k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8642, c_72])).
% 12.02/4.60  tff(c_8836, plain, (v1_funct_2(k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4')), k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8512, c_8509, c_8809])).
% 12.02/4.60  tff(c_8194, plain, (![A_450, B_451, C_452]: (m1_subset_1(k2_tops_2(A_450, B_451, C_452), k1_zfmisc_1(k2_zfmisc_1(B_451, A_450))) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))) | ~v1_funct_2(C_452, A_450, B_451) | ~v1_funct_1(C_452))), inference(cnfTransformation, [status(thm)], [f_184])).
% 12.02/4.60  tff(c_8241, plain, (![B_451, C_452]: (k2_tops_2(k1_xboole_0, B_451, C_452)=k1_xboole_0 | ~v1_funct_2(k2_tops_2(k1_xboole_0, B_451, C_452), B_451, k1_xboole_0) | k1_xboole_0=B_451 | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_451))) | ~v1_funct_2(C_452, k1_xboole_0, B_451) | ~v1_funct_1(C_452))), inference(resolution, [status(thm)], [c_8194, c_28])).
% 12.02/4.60  tff(c_19100, plain, (![B_795, C_796]: (k2_tops_2('#skF_4', B_795, C_796)='#skF_4' | ~v1_funct_2(k2_tops_2('#skF_4', B_795, C_796), B_795, '#skF_4') | B_795='#skF_4' | ~m1_subset_1(C_796, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_795))) | ~v1_funct_2(C_796, '#skF_4', B_795) | ~v1_funct_1(C_796))), inference(demodulation, [status(thm), theory('equality')], [c_8192, c_8192, c_8192, c_8192, c_8192, c_8192, c_8192, c_8241])).
% 12.02/4.60  tff(c_19107, plain, (k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4'))='#skF_4' | k2_struct_0('#skF_2')='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_struct_0('#skF_2')))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8836, c_19100])).
% 12.02/4.60  tff(c_19120, plain, (k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4'))='#skF_4' | k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8512, c_8509, c_8642, c_19107])).
% 12.02/4.60  tff(c_19121, plain, (k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_8286, c_19120])).
% 12.02/4.60  tff(c_7904, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k1_xboole_0, k2_tops_2(k1_xboole_0, k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_xboole_0, '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7899, c_7899, c_7899, c_265])).
% 12.02/4.60  tff(c_8287, plain, (~r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8192, c_8192, c_8192, c_7904])).
% 12.02/4.60  tff(c_8627, plain, (~r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8287])).
% 12.02/4.60  tff(c_19199, plain, (~r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19121, c_8627])).
% 12.02/4.60  tff(c_19205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9021, c_19199])).
% 12.02/4.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.02/4.60  
% 12.02/4.60  Inference rules
% 12.02/4.60  ----------------------
% 12.02/4.60  #Ref     : 0
% 12.02/4.60  #Sup     : 4008
% 12.02/4.60  #Fact    : 1
% 12.02/4.60  #Define  : 0
% 12.02/4.60  #Split   : 35
% 12.02/4.60  #Chain   : 0
% 12.02/4.60  #Close   : 0
% 12.02/4.60  
% 12.02/4.60  Ordering : KBO
% 12.02/4.60  
% 12.02/4.60  Simplification rules
% 12.02/4.60  ----------------------
% 12.02/4.60  #Subsume      : 617
% 12.02/4.60  #Demod        : 4855
% 12.02/4.60  #Tautology    : 1613
% 12.02/4.60  #SimpNegUnit  : 227
% 12.02/4.60  #BackRed      : 186
% 12.02/4.60  
% 12.02/4.60  #Partial instantiations: 0
% 12.02/4.60  #Strategies tried      : 1
% 12.02/4.60  
% 12.02/4.60  Timing (in seconds)
% 12.02/4.60  ----------------------
% 12.02/4.60  Preprocessing        : 0.38
% 12.02/4.60  Parsing              : 0.20
% 12.02/4.60  CNF conversion       : 0.03
% 12.02/4.60  Main loop            : 3.42
% 12.02/4.60  Inferencing          : 1.00
% 12.02/4.60  Reduction            : 1.35
% 12.02/4.60  Demodulation         : 1.06
% 12.02/4.60  BG Simplification    : 0.10
% 12.02/4.60  Subsumption          : 0.74
% 12.02/4.60  Abstraction          : 0.13
% 12.02/4.60  MUC search           : 0.00
% 12.02/4.60  Cooper               : 0.00
% 12.02/4.60  Total                : 3.87
% 12.02/4.60  Index Insertion      : 0.00
% 12.02/4.60  Index Deletion       : 0.00
% 12.02/4.60  Index Matching       : 0.00
% 12.02/4.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
