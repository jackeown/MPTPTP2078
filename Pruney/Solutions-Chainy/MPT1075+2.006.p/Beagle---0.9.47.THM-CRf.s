%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:11 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 507 expanded)
%              Number of leaves         :   45 ( 199 expanded)
%              Depth                    :   17
%              Number of atoms          :  405 (2183 expanded)
%              Number of equality atoms :   69 ( 277 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_171,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( k1_relset_1(A,B,C) = A
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_147,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_50,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_203,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k3_funct_2(A_135,B_136,C_137,D_138) = k1_funct_1(C_137,D_138)
      | ~ m1_subset_1(D_138,A_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_2(C_137,A_135,B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_213,plain,(
    ! [B_136,C_137] :
      ( k3_funct_2('#skF_2',B_136,C_137,'#skF_6') = k1_funct_1(C_137,'#skF_6')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_136)))
      | ~ v1_funct_2(C_137,'#skF_2',B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_203])).

tff(c_225,plain,(
    ! [B_139,C_140] :
      ( k3_funct_2('#skF_2',B_139,C_140,'#skF_6') = k1_funct_1(C_140,'#skF_6')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_139)))
      | ~ v1_funct_2(C_140,'#skF_2',B_139)
      | ~ v1_funct_1(C_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_213])).

tff(c_228,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_225])).

tff(c_231,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_228])).

tff(c_46,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_232,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_46])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_247,plain,(
    ! [E_143,B_144,A_145,D_142,C_141] :
      ( v1_funct_1(k8_funct_2(A_145,B_144,C_141,D_142,E_143))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(B_144,C_141)))
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144)))
      | ~ v1_funct_2(D_142,A_145,B_144)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_251,plain,(
    ! [A_145,D_142] :
      ( v1_funct_1(k8_funct_2(A_145,'#skF_1','#skF_3',D_142,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_145,'#skF_1')))
      | ~ v1_funct_2(D_142,A_145,'#skF_1')
      | ~ v1_funct_1(D_142) ) ),
    inference(resolution,[status(thm)],[c_52,c_247])).

tff(c_259,plain,(
    ! [A_148,D_149] :
      ( v1_funct_1(k8_funct_2(A_148,'#skF_1','#skF_3',D_149,'#skF_5'))
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_148,'#skF_1')))
      | ~ v1_funct_2(D_149,A_148,'#skF_1')
      | ~ v1_funct_1(D_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_251])).

tff(c_262,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_259])).

tff(c_265,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_262])).

tff(c_327,plain,(
    ! [C_158,B_161,D_159,A_162,E_160] :
      ( v1_funct_2(k8_funct_2(A_162,B_161,C_158,D_159,E_160),A_162,C_158)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(B_161,C_158)))
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161)))
      | ~ v1_funct_2(D_159,A_162,B_161)
      | ~ v1_funct_1(D_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_331,plain,(
    ! [A_162,D_159] :
      ( v1_funct_2(k8_funct_2(A_162,'#skF_1','#skF_3',D_159,'#skF_5'),A_162,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_162,'#skF_1')))
      | ~ v1_funct_2(D_159,A_162,'#skF_1')
      | ~ v1_funct_1(D_159) ) ),
    inference(resolution,[status(thm)],[c_52,c_327])).

tff(c_342,plain,(
    ! [A_163,D_164] :
      ( v1_funct_2(k8_funct_2(A_163,'#skF_1','#skF_3',D_164,'#skF_5'),A_163,'#skF_3')
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_163,'#skF_1')))
      | ~ v1_funct_2(D_164,A_163,'#skF_1')
      | ~ v1_funct_1(D_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_331])).

tff(c_344,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_342])).

tff(c_347,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_344])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_66])).

tff(c_75,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_94,plain,(
    ! [C_111,B_112,A_113] :
      ( v5_relat_1(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_48,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_80,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_104,plain,(
    ! [B_115,A_116] :
      ( k1_relat_1(B_115) = A_116
      | ~ v1_partfun1(B_115,A_116)
      | ~ v4_relat_1(B_115,A_116)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_107,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_104])).

tff(c_113,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_48,c_107])).

tff(c_144,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_150,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_144])).

tff(c_153,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_150])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_117,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_117])).

tff(c_465,plain,(
    ! [B_183,D_184,F_185,C_181,A_182,E_186] :
      ( k7_partfun1(A_182,E_186,k1_funct_1(D_184,F_185)) = k1_funct_1(k8_funct_2(B_183,C_181,A_182,D_184,E_186),F_185)
      | k1_xboole_0 = B_183
      | ~ r1_tarski(k2_relset_1(B_183,C_181,D_184),k1_relset_1(C_181,A_182,E_186))
      | ~ m1_subset_1(F_185,B_183)
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(C_181,A_182)))
      | ~ v1_funct_1(E_186)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_183,C_181)))
      | ~ v1_funct_2(D_184,B_183,C_181)
      | ~ v1_funct_1(D_184)
      | v1_xboole_0(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_473,plain,(
    ! [A_182,E_186,F_185] :
      ( k7_partfun1(A_182,E_186,k1_funct_1('#skF_4',F_185)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_182,'#skF_4',E_186),F_185)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_182,E_186))
      | ~ m1_subset_1(F_185,'#skF_2')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_182)))
      | ~ v1_funct_1(E_186)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_465])).

tff(c_484,plain,(
    ! [A_182,E_186,F_185] :
      ( k7_partfun1(A_182,E_186,k1_funct_1('#skF_4',F_185)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_182,'#skF_4',E_186),F_185)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_182,E_186))
      | ~ m1_subset_1(F_185,'#skF_2')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_182)))
      | ~ v1_funct_1(E_186)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_473])).

tff(c_485,plain,(
    ! [A_182,E_186,F_185] :
      ( k7_partfun1(A_182,E_186,k1_funct_1('#skF_4',F_185)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_182,'#skF_4',E_186),F_185)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_182,E_186))
      | ~ m1_subset_1(F_185,'#skF_2')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_182)))
      | ~ v1_funct_1(E_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_484])).

tff(c_629,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_631,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_2])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_631])).

tff(c_636,plain,(
    ! [A_224,E_225,F_226] :
      ( k7_partfun1(A_224,E_225,k1_funct_1('#skF_4',F_226)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_224,'#skF_4',E_225),F_226)
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_224,E_225))
      | ~ m1_subset_1(F_226,'#skF_2')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_224)))
      | ~ v1_funct_1(E_225) ) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_638,plain,(
    ! [F_226] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_226)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_226)
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_226,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_636])).

tff(c_643,plain,(
    ! [F_226] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_226)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_226)
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_226,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_638])).

tff(c_647,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_650,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_647])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_101,c_650])).

tff(c_677,plain,(
    ! [F_232] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_232)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_232)
      | ~ m1_subset_1(F_232,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_162,plain,(
    ! [C_123,A_124,B_125] :
      ( ~ v1_partfun1(C_123,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_xboole_0(B_125)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_168,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_162])).

tff(c_173,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_168])).

tff(c_174,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_173])).

tff(c_175,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_funct_2(C_126,A_127,B_128)
      | k1_relset_1(A_127,B_128,C_126) != A_127
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_181,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_5') != '#skF_1'
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_175])).

tff(c_187,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_153,c_181])).

tff(c_188,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( m1_subset_1(k3_funct_2(A_129,B_130,C_131,D_132),B_130)
      | ~ m1_subset_1(D_132,A_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_2(C_131,A_129,B_130)
      | ~ v1_funct_1(C_131)
      | v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_190,plain,(
    ! [D_132] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_132),'#skF_1')
      | ~ m1_subset_1(D_132,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_188])).

tff(c_195,plain,(
    ! [D_132] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_132),'#skF_1')
      | ~ m1_subset_1(D_132,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_190])).

tff(c_196,plain,(
    ! [D_132] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_132),'#skF_1')
      | ~ m1_subset_1(D_132,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_195])).

tff(c_236,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_196])).

tff(c_240,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_236])).

tff(c_34,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k3_funct_2(A_32,B_33,C_34,D_35) = k1_funct_1(C_34,D_35)
      | ~ m1_subset_1(D_35,A_32)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_243,plain,(
    ! [B_33,C_34] :
      ( k3_funct_2('#skF_1',B_33,C_34,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_34,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_33)))
      | ~ v1_funct_2(C_34,'#skF_1',B_33)
      | ~ v1_funct_1(C_34)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_240,c_34])).

tff(c_266,plain,(
    ! [B_150,C_151] :
      ( k3_funct_2('#skF_1',B_150,C_151,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_151,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_150)))
      | ~ v1_funct_2(C_151,'#skF_1',B_150)
      | ~ v1_funct_1(C_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_243])).

tff(c_269,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_266])).

tff(c_272,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_187,c_269])).

tff(c_287,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k3_funct_2(A_152,B_153,C_154,D_155) = k7_partfun1(B_153,C_154,D_155)
      | ~ m1_subset_1(D_155,A_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_2(C_154,A_152,B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_291,plain,(
    ! [B_153,C_154] :
      ( k3_funct_2('#skF_1',B_153,C_154,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_153,C_154,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_153)))
      | ~ v1_funct_2(C_154,'#skF_1',B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_240,c_287])).

tff(c_348,plain,(
    ! [B_165,C_166] :
      ( k3_funct_2('#skF_1',B_165,C_166,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_165,C_166,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_165)))
      | ~ v1_funct_2(C_166,'#skF_1',B_165)
      | ~ v1_funct_1(C_166)
      | v1_xboole_0(B_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_291])).

tff(c_351,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_348])).

tff(c_354,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_187,c_272,c_351])).

tff(c_355,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_354])).

tff(c_683,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_355])).

tff(c_692,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_683])).

tff(c_28,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] :
      ( m1_subset_1(k8_funct_2(A_27,B_28,C_29,D_30,E_31),k1_zfmisc_1(k2_zfmisc_1(A_27,C_29)))
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(B_28,C_29)))
      | ~ v1_funct_1(E_31)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(D_30,A_27,B_28)
      | ~ v1_funct_1(D_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_362,plain,(
    ! [C_171,E_173,D_172,B_174,A_175] :
      ( m1_subset_1(k8_funct_2(A_175,B_174,C_171,D_172,E_173),k1_zfmisc_1(k2_zfmisc_1(A_175,C_171)))
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(B_174,C_171)))
      | ~ v1_funct_1(E_173)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_175,B_174)))
      | ~ v1_funct_2(D_172,A_175,B_174)
      | ~ v1_funct_1(D_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_657,plain,(
    ! [D_227,A_228,C_229,E_231,B_230] :
      ( k1_relset_1(A_228,C_229,k8_funct_2(A_228,B_230,C_229,D_227,E_231)) = k1_relat_1(k8_funct_2(A_228,B_230,C_229,D_227,E_231))
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(B_230,C_229)))
      | ~ v1_funct_1(E_231)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_230)))
      | ~ v1_funct_2(D_227,A_228,B_230)
      | ~ v1_funct_1(D_227) ) ),
    inference(resolution,[status(thm)],[c_362,c_16])).

tff(c_663,plain,(
    ! [A_228,D_227] :
      ( k1_relset_1(A_228,'#skF_3',k8_funct_2(A_228,'#skF_1','#skF_3',D_227,'#skF_5')) = k1_relat_1(k8_funct_2(A_228,'#skF_1','#skF_3',D_227,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_228,'#skF_1')))
      | ~ v1_funct_2(D_227,A_228,'#skF_1')
      | ~ v1_funct_1(D_227) ) ),
    inference(resolution,[status(thm)],[c_52,c_657])).

tff(c_787,plain,(
    ! [A_246,D_247] :
      ( k1_relset_1(A_246,'#skF_3',k8_funct_2(A_246,'#skF_1','#skF_3',D_247,'#skF_5')) = k1_relat_1(k8_funct_2(A_246,'#skF_1','#skF_3',D_247,'#skF_5'))
      | ~ m1_subset_1(D_247,k1_zfmisc_1(k2_zfmisc_1(A_246,'#skF_1')))
      | ~ v1_funct_2(D_247,A_246,'#skF_1')
      | ~ v1_funct_1(D_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_663])).

tff(c_792,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_787])).

tff(c_796,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_792])).

tff(c_44,plain,(
    ! [F_70,C_56,D_64,E_68,B_55,A_54] :
      ( k7_partfun1(A_54,E_68,k1_funct_1(D_64,F_70)) = k1_funct_1(k8_funct_2(B_55,C_56,A_54,D_64,E_68),F_70)
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,C_56,D_64),k1_relset_1(C_56,A_54,E_68))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(C_56,A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,C_56)))
      | ~ v1_funct_2(D_64,B_55,C_56)
      | ~ v1_funct_1(D_64)
      | v1_xboole_0(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_799,plain,(
    ! [D_64,F_70,B_55] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_64,F_70)) = k1_funct_1(k8_funct_2(B_55,'#skF_2','#skF_3',D_64,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_70)
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,'#skF_2',D_64),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,'#skF_2')))
      | ~ v1_funct_2(D_64,B_55,'#skF_2')
      | ~ v1_funct_1(D_64)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_44])).

tff(c_803,plain,(
    ! [D_64,F_70,B_55] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_64,F_70)) = k1_funct_1(k8_funct_2(B_55,'#skF_2','#skF_3',D_64,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_70)
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,'#skF_2',D_64),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,'#skF_2')))
      | ~ v1_funct_2(D_64,B_55,'#skF_2')
      | ~ v1_funct_1(D_64)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_799])).

tff(c_804,plain,(
    ! [D_64,F_70,B_55] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_64,F_70)) = k1_funct_1(k8_funct_2(B_55,'#skF_2','#skF_3',D_64,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_70)
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,'#skF_2',D_64),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,'#skF_2')))
      | ~ v1_funct_2(D_64,B_55,'#skF_2')
      | ~ v1_funct_1(D_64) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_803])).

tff(c_925,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_804])).

tff(c_928,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_925])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_928])).

tff(c_934,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_804])).

tff(c_224,plain,(
    ! [B_136,C_137] :
      ( k3_funct_2('#skF_2',B_136,C_137,'#skF_6') = k1_funct_1(C_137,'#skF_6')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_136)))
      | ~ v1_funct_2(C_137,'#skF_2',B_136)
      | ~ v1_funct_1(C_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_213])).

tff(c_960,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_934,c_224])).

tff(c_1020,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_347,c_692,c_960])).

tff(c_1022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_1020])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.73  
% 4.01/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.01/1.73  
% 4.01/1.73  %Foreground sorts:
% 4.01/1.73  
% 4.01/1.73  
% 4.01/1.73  %Background operators:
% 4.01/1.73  
% 4.01/1.73  
% 4.01/1.73  %Foreground operators:
% 4.01/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.01/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.73  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.01/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.01/1.73  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.01/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.01/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.73  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.01/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.01/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.01/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.01/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.01/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.73  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.01/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.01/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.73  
% 4.01/1.77  tff(f_198, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 4.01/1.77  tff(f_116, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.01/1.77  tff(f_103, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 4.01/1.77  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.01/1.77  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.01/1.77  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.01/1.77  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.01/1.77  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.01/1.77  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.01/1.77  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.01/1.77  tff(f_171, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 4.01/1.77  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.01/1.77  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 4.01/1.77  tff(f_128, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 4.01/1.77  tff(f_87, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 4.01/1.77  tff(f_147, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 4.01/1.77  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_50, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_203, plain, (![A_135, B_136, C_137, D_138]: (k3_funct_2(A_135, B_136, C_137, D_138)=k1_funct_1(C_137, D_138) | ~m1_subset_1(D_138, A_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_2(C_137, A_135, B_136) | ~v1_funct_1(C_137) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.01/1.77  tff(c_213, plain, (![B_136, C_137]: (k3_funct_2('#skF_2', B_136, C_137, '#skF_6')=k1_funct_1(C_137, '#skF_6') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_136))) | ~v1_funct_2(C_137, '#skF_2', B_136) | ~v1_funct_1(C_137) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_203])).
% 4.01/1.77  tff(c_225, plain, (![B_139, C_140]: (k3_funct_2('#skF_2', B_139, C_140, '#skF_6')=k1_funct_1(C_140, '#skF_6') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_139))) | ~v1_funct_2(C_140, '#skF_2', B_139) | ~v1_funct_1(C_140))), inference(negUnitSimplification, [status(thm)], [c_62, c_213])).
% 4.01/1.77  tff(c_228, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_225])).
% 4.01/1.77  tff(c_231, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_228])).
% 4.01/1.77  tff(c_46, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_232, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_46])).
% 4.01/1.77  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.77  tff(c_247, plain, (![E_143, B_144, A_145, D_142, C_141]: (v1_funct_1(k8_funct_2(A_145, B_144, C_141, D_142, E_143)) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(B_144, C_141))) | ~v1_funct_1(E_143) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))) | ~v1_funct_2(D_142, A_145, B_144) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.01/1.77  tff(c_251, plain, (![A_145, D_142]: (v1_funct_1(k8_funct_2(A_145, '#skF_1', '#skF_3', D_142, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_145, '#skF_1'))) | ~v1_funct_2(D_142, A_145, '#skF_1') | ~v1_funct_1(D_142))), inference(resolution, [status(thm)], [c_52, c_247])).
% 4.01/1.77  tff(c_259, plain, (![A_148, D_149]: (v1_funct_1(k8_funct_2(A_148, '#skF_1', '#skF_3', D_149, '#skF_5')) | ~m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(A_148, '#skF_1'))) | ~v1_funct_2(D_149, A_148, '#skF_1') | ~v1_funct_1(D_149))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_251])).
% 4.01/1.77  tff(c_262, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_259])).
% 4.01/1.77  tff(c_265, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_262])).
% 4.01/1.78  tff(c_327, plain, (![C_158, B_161, D_159, A_162, E_160]: (v1_funct_2(k8_funct_2(A_162, B_161, C_158, D_159, E_160), A_162, C_158) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(B_161, C_158))) | ~v1_funct_1(E_160) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))) | ~v1_funct_2(D_159, A_162, B_161) | ~v1_funct_1(D_159))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.01/1.78  tff(c_331, plain, (![A_162, D_159]: (v1_funct_2(k8_funct_2(A_162, '#skF_1', '#skF_3', D_159, '#skF_5'), A_162, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_162, '#skF_1'))) | ~v1_funct_2(D_159, A_162, '#skF_1') | ~v1_funct_1(D_159))), inference(resolution, [status(thm)], [c_52, c_327])).
% 4.01/1.78  tff(c_342, plain, (![A_163, D_164]: (v1_funct_2(k8_funct_2(A_163, '#skF_1', '#skF_3', D_164, '#skF_5'), A_163, '#skF_3') | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_163, '#skF_1'))) | ~v1_funct_2(D_164, A_163, '#skF_1') | ~v1_funct_1(D_164))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_331])).
% 4.01/1.78  tff(c_344, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_342])).
% 4.01/1.78  tff(c_347, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_344])).
% 4.01/1.78  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.01/1.78  tff(c_66, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.01/1.78  tff(c_69, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_66])).
% 4.01/1.78  tff(c_75, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 4.01/1.78  tff(c_94, plain, (![C_111, B_112, A_113]: (v5_relat_1(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.01/1.78  tff(c_101, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_94])).
% 4.01/1.78  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.01/1.78  tff(c_72, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_66])).
% 4.01/1.78  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 4.01/1.78  tff(c_48, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.78  tff(c_80, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.01/1.78  tff(c_88, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_80])).
% 4.01/1.78  tff(c_104, plain, (![B_115, A_116]: (k1_relat_1(B_115)=A_116 | ~v1_partfun1(B_115, A_116) | ~v4_relat_1(B_115, A_116) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.01/1.78  tff(c_107, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_104])).
% 4.01/1.78  tff(c_113, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_48, c_107])).
% 4.01/1.78  tff(c_144, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.01/1.78  tff(c_150, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_144])).
% 4.01/1.78  tff(c_153, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_150])).
% 4.01/1.78  tff(c_64, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 4.01/1.78  tff(c_117, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.01/1.78  tff(c_124, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_117])).
% 4.01/1.78  tff(c_465, plain, (![B_183, D_184, F_185, C_181, A_182, E_186]: (k7_partfun1(A_182, E_186, k1_funct_1(D_184, F_185))=k1_funct_1(k8_funct_2(B_183, C_181, A_182, D_184, E_186), F_185) | k1_xboole_0=B_183 | ~r1_tarski(k2_relset_1(B_183, C_181, D_184), k1_relset_1(C_181, A_182, E_186)) | ~m1_subset_1(F_185, B_183) | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(C_181, A_182))) | ~v1_funct_1(E_186) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_183, C_181))) | ~v1_funct_2(D_184, B_183, C_181) | ~v1_funct_1(D_184) | v1_xboole_0(C_181))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.01/1.78  tff(c_473, plain, (![A_182, E_186, F_185]: (k7_partfun1(A_182, E_186, k1_funct_1('#skF_4', F_185))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_182, '#skF_4', E_186), F_185) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_182, E_186)) | ~m1_subset_1(F_185, '#skF_2') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_182))) | ~v1_funct_1(E_186) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_465])).
% 4.01/1.78  tff(c_484, plain, (![A_182, E_186, F_185]: (k7_partfun1(A_182, E_186, k1_funct_1('#skF_4', F_185))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_182, '#skF_4', E_186), F_185) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_182, E_186)) | ~m1_subset_1(F_185, '#skF_2') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_182))) | ~v1_funct_1(E_186) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_473])).
% 4.01/1.78  tff(c_485, plain, (![A_182, E_186, F_185]: (k7_partfun1(A_182, E_186, k1_funct_1('#skF_4', F_185))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_182, '#skF_4', E_186), F_185) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_182, E_186)) | ~m1_subset_1(F_185, '#skF_2') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_182))) | ~v1_funct_1(E_186))), inference(negUnitSimplification, [status(thm)], [c_64, c_484])).
% 4.01/1.78  tff(c_629, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_485])).
% 4.01/1.78  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.01/1.78  tff(c_631, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_629, c_2])).
% 4.01/1.78  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_631])).
% 4.01/1.78  tff(c_636, plain, (![A_224, E_225, F_226]: (k7_partfun1(A_224, E_225, k1_funct_1('#skF_4', F_226))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_224, '#skF_4', E_225), F_226) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_224, E_225)) | ~m1_subset_1(F_226, '#skF_2') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_224))) | ~v1_funct_1(E_225))), inference(splitRight, [status(thm)], [c_485])).
% 4.01/1.78  tff(c_638, plain, (![F_226]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_226))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_226) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_226, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_636])).
% 4.01/1.78  tff(c_643, plain, (![F_226]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_226))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_226) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_226, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_638])).
% 4.01/1.78  tff(c_647, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_643])).
% 4.01/1.78  tff(c_650, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_647])).
% 4.01/1.78  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_101, c_650])).
% 4.01/1.78  tff(c_677, plain, (![F_232]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_232))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_232) | ~m1_subset_1(F_232, '#skF_2'))), inference(splitRight, [status(thm)], [c_643])).
% 4.01/1.78  tff(c_162, plain, (![C_123, A_124, B_125]: (~v1_partfun1(C_123, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_xboole_0(B_125) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.01/1.78  tff(c_168, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_162])).
% 4.01/1.78  tff(c_173, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_168])).
% 4.01/1.78  tff(c_174, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_173])).
% 4.01/1.78  tff(c_175, plain, (![C_126, A_127, B_128]: (v1_funct_2(C_126, A_127, B_128) | k1_relset_1(A_127, B_128, C_126)!=A_127 | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.01/1.78  tff(c_181, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_5')!='#skF_1' | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_175])).
% 4.01/1.78  tff(c_187, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_153, c_181])).
% 4.01/1.78  tff(c_188, plain, (![A_129, B_130, C_131, D_132]: (m1_subset_1(k3_funct_2(A_129, B_130, C_131, D_132), B_130) | ~m1_subset_1(D_132, A_129) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_2(C_131, A_129, B_130) | ~v1_funct_1(C_131) | v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.01/1.78  tff(c_190, plain, (![D_132]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_132), '#skF_1') | ~m1_subset_1(D_132, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_188])).
% 4.01/1.78  tff(c_195, plain, (![D_132]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_132), '#skF_1') | ~m1_subset_1(D_132, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_190])).
% 4.01/1.78  tff(c_196, plain, (![D_132]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_132), '#skF_1') | ~m1_subset_1(D_132, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_195])).
% 4.01/1.78  tff(c_236, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_196])).
% 4.01/1.78  tff(c_240, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_236])).
% 4.01/1.78  tff(c_34, plain, (![A_32, B_33, C_34, D_35]: (k3_funct_2(A_32, B_33, C_34, D_35)=k1_funct_1(C_34, D_35) | ~m1_subset_1(D_35, A_32) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.01/1.78  tff(c_243, plain, (![B_33, C_34]: (k3_funct_2('#skF_1', B_33, C_34, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_34, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_33))) | ~v1_funct_2(C_34, '#skF_1', B_33) | ~v1_funct_1(C_34) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_240, c_34])).
% 4.01/1.78  tff(c_266, plain, (![B_150, C_151]: (k3_funct_2('#skF_1', B_150, C_151, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_151, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_150))) | ~v1_funct_2(C_151, '#skF_1', B_150) | ~v1_funct_1(C_151))), inference(negUnitSimplification, [status(thm)], [c_64, c_243])).
% 4.01/1.78  tff(c_269, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_266])).
% 4.01/1.78  tff(c_272, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_187, c_269])).
% 4.01/1.78  tff(c_287, plain, (![A_152, B_153, C_154, D_155]: (k3_funct_2(A_152, B_153, C_154, D_155)=k7_partfun1(B_153, C_154, D_155) | ~m1_subset_1(D_155, A_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_2(C_154, A_152, B_153) | ~v1_funct_1(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.01/1.78  tff(c_291, plain, (![B_153, C_154]: (k3_funct_2('#skF_1', B_153, C_154, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_153, C_154, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_153))) | ~v1_funct_2(C_154, '#skF_1', B_153) | ~v1_funct_1(C_154) | v1_xboole_0(B_153) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_240, c_287])).
% 4.01/1.78  tff(c_348, plain, (![B_165, C_166]: (k3_funct_2('#skF_1', B_165, C_166, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_165, C_166, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_165))) | ~v1_funct_2(C_166, '#skF_1', B_165) | ~v1_funct_1(C_166) | v1_xboole_0(B_165))), inference(negUnitSimplification, [status(thm)], [c_64, c_291])).
% 4.01/1.78  tff(c_351, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_348])).
% 4.01/1.78  tff(c_354, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_187, c_272, c_351])).
% 4.01/1.78  tff(c_355, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_174, c_354])).
% 4.01/1.78  tff(c_683, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_677, c_355])).
% 4.01/1.78  tff(c_692, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_683])).
% 4.01/1.78  tff(c_28, plain, (![C_29, D_30, B_28, A_27, E_31]: (m1_subset_1(k8_funct_2(A_27, B_28, C_29, D_30, E_31), k1_zfmisc_1(k2_zfmisc_1(A_27, C_29))) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(B_28, C_29))) | ~v1_funct_1(E_31) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(D_30, A_27, B_28) | ~v1_funct_1(D_30))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.01/1.78  tff(c_362, plain, (![C_171, E_173, D_172, B_174, A_175]: (m1_subset_1(k8_funct_2(A_175, B_174, C_171, D_172, E_173), k1_zfmisc_1(k2_zfmisc_1(A_175, C_171))) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(B_174, C_171))) | ~v1_funct_1(E_173) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_175, B_174))) | ~v1_funct_2(D_172, A_175, B_174) | ~v1_funct_1(D_172))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.01/1.78  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.01/1.78  tff(c_657, plain, (![D_227, A_228, C_229, E_231, B_230]: (k1_relset_1(A_228, C_229, k8_funct_2(A_228, B_230, C_229, D_227, E_231))=k1_relat_1(k8_funct_2(A_228, B_230, C_229, D_227, E_231)) | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(B_230, C_229))) | ~v1_funct_1(E_231) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_230))) | ~v1_funct_2(D_227, A_228, B_230) | ~v1_funct_1(D_227))), inference(resolution, [status(thm)], [c_362, c_16])).
% 4.01/1.78  tff(c_663, plain, (![A_228, D_227]: (k1_relset_1(A_228, '#skF_3', k8_funct_2(A_228, '#skF_1', '#skF_3', D_227, '#skF_5'))=k1_relat_1(k8_funct_2(A_228, '#skF_1', '#skF_3', D_227, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_228, '#skF_1'))) | ~v1_funct_2(D_227, A_228, '#skF_1') | ~v1_funct_1(D_227))), inference(resolution, [status(thm)], [c_52, c_657])).
% 4.01/1.78  tff(c_787, plain, (![A_246, D_247]: (k1_relset_1(A_246, '#skF_3', k8_funct_2(A_246, '#skF_1', '#skF_3', D_247, '#skF_5'))=k1_relat_1(k8_funct_2(A_246, '#skF_1', '#skF_3', D_247, '#skF_5')) | ~m1_subset_1(D_247, k1_zfmisc_1(k2_zfmisc_1(A_246, '#skF_1'))) | ~v1_funct_2(D_247, A_246, '#skF_1') | ~v1_funct_1(D_247))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_663])).
% 4.01/1.78  tff(c_792, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_787])).
% 4.01/1.78  tff(c_796, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_792])).
% 4.01/1.78  tff(c_44, plain, (![F_70, C_56, D_64, E_68, B_55, A_54]: (k7_partfun1(A_54, E_68, k1_funct_1(D_64, F_70))=k1_funct_1(k8_funct_2(B_55, C_56, A_54, D_64, E_68), F_70) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, C_56, D_64), k1_relset_1(C_56, A_54, E_68)) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(C_56, A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, C_56))) | ~v1_funct_2(D_64, B_55, C_56) | ~v1_funct_1(D_64) | v1_xboole_0(C_56))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.01/1.78  tff(c_799, plain, (![D_64, F_70, B_55]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_64, F_70))=k1_funct_1(k8_funct_2(B_55, '#skF_2', '#skF_3', D_64, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_70) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, '#skF_2', D_64), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, '#skF_2'))) | ~v1_funct_2(D_64, B_55, '#skF_2') | ~v1_funct_1(D_64) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_796, c_44])).
% 4.01/1.78  tff(c_803, plain, (![D_64, F_70, B_55]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_64, F_70))=k1_funct_1(k8_funct_2(B_55, '#skF_2', '#skF_3', D_64, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_70) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, '#skF_2', D_64), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, '#skF_2'))) | ~v1_funct_2(D_64, B_55, '#skF_2') | ~v1_funct_1(D_64) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_799])).
% 4.01/1.78  tff(c_804, plain, (![D_64, F_70, B_55]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_64, F_70))=k1_funct_1(k8_funct_2(B_55, '#skF_2', '#skF_3', D_64, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_70) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, '#skF_2', D_64), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, '#skF_2'))) | ~v1_funct_2(D_64, B_55, '#skF_2') | ~v1_funct_1(D_64))), inference(negUnitSimplification, [status(thm)], [c_62, c_803])).
% 4.01/1.78  tff(c_925, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_804])).
% 4.01/1.78  tff(c_928, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_925])).
% 4.01/1.78  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_928])).
% 4.01/1.78  tff(c_934, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_804])).
% 4.01/1.78  tff(c_224, plain, (![B_136, C_137]: (k3_funct_2('#skF_2', B_136, C_137, '#skF_6')=k1_funct_1(C_137, '#skF_6') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_136))) | ~v1_funct_2(C_137, '#skF_2', B_136) | ~v1_funct_1(C_137))), inference(negUnitSimplification, [status(thm)], [c_62, c_213])).
% 4.01/1.78  tff(c_960, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_934, c_224])).
% 4.01/1.78  tff(c_1020, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_347, c_692, c_960])).
% 4.01/1.78  tff(c_1022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_1020])).
% 4.01/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.78  
% 4.01/1.78  Inference rules
% 4.01/1.78  ----------------------
% 4.01/1.78  #Ref     : 0
% 4.01/1.78  #Sup     : 200
% 4.01/1.78  #Fact    : 0
% 4.01/1.78  #Define  : 0
% 4.01/1.78  #Split   : 8
% 4.01/1.78  #Chain   : 0
% 4.01/1.78  #Close   : 0
% 4.01/1.78  
% 4.01/1.78  Ordering : KBO
% 4.01/1.78  
% 4.01/1.78  Simplification rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Subsume      : 6
% 4.39/1.78  #Demod        : 152
% 4.39/1.78  #Tautology    : 47
% 4.39/1.78  #SimpNegUnit  : 32
% 4.39/1.78  #BackRed      : 6
% 4.39/1.78  
% 4.39/1.78  #Partial instantiations: 0
% 4.39/1.78  #Strategies tried      : 1
% 4.39/1.78  
% 4.39/1.78  Timing (in seconds)
% 4.39/1.78  ----------------------
% 4.41/1.79  Preprocessing        : 0.40
% 4.41/1.79  Parsing              : 0.22
% 4.41/1.79  CNF conversion       : 0.03
% 4.41/1.79  Main loop            : 0.53
% 4.41/1.79  Inferencing          : 0.19
% 4.41/1.79  Reduction            : 0.17
% 4.41/1.79  Demodulation         : 0.12
% 4.41/1.79  BG Simplification    : 0.03
% 4.41/1.79  Subsumption          : 0.10
% 4.41/1.79  Abstraction          : 0.03
% 4.41/1.79  MUC search           : 0.00
% 4.41/1.79  Cooper               : 0.00
% 4.41/1.79  Total                : 1.01
% 4.41/1.79  Index Insertion      : 0.00
% 4.41/1.79  Index Deletion       : 0.00
% 4.41/1.79  Index Matching       : 0.00
% 4.41/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
