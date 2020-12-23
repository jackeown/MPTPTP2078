%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:14 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 238 expanded)
%              Number of leaves         :   41 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  205 (1310 expanded)
%              Number of equality atoms :   32 ( 117 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ( r1_tarski(F,u1_struct_0(C))
                               => k7_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k7_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tmap_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_32,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_79,plain,(
    ! [B_132,A_133] :
      ( v1_relat_1(B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133))
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_82])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_219,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k2_partfun1(A_167,B_168,C_169,D_170) = k7_relat_1(C_169,D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_funct_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_224,plain,(
    ! [D_170] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_170) = k7_relat_1('#skF_5',D_170)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_219])).

tff(c_231,plain,(
    ! [D_170] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_170) = k7_relat_1('#skF_5',D_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_224])).

tff(c_478,plain,(
    ! [D_220,C_221,E_218,B_217,A_219] :
      ( k3_tmap_1(A_219,B_217,C_221,D_220,E_218) = k2_partfun1(u1_struct_0(C_221),u1_struct_0(B_217),E_218,u1_struct_0(D_220))
      | ~ m1_pre_topc(D_220,C_221)
      | ~ m1_subset_1(E_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_221),u1_struct_0(B_217))))
      | ~ v1_funct_2(E_218,u1_struct_0(C_221),u1_struct_0(B_217))
      | ~ v1_funct_1(E_218)
      | ~ m1_pre_topc(D_220,A_219)
      | ~ m1_pre_topc(C_221,A_219)
      | ~ l1_pre_topc(B_217)
      | ~ v2_pre_topc(B_217)
      | v2_struct_0(B_217)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_491,plain,(
    ! [A_219,D_220] :
      ( k3_tmap_1(A_219,'#skF_2','#skF_4',D_220,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_220))
      | ~ m1_pre_topc(D_220,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_220,A_219)
      | ~ m1_pre_topc('#skF_4',A_219)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_38,c_478])).

tff(c_504,plain,(
    ! [D_220,A_219] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_220)) = k3_tmap_1(A_219,'#skF_2','#skF_4',D_220,'#skF_5')
      | ~ m1_pre_topc(D_220,'#skF_4')
      | ~ m1_pre_topc(D_220,A_219)
      | ~ m1_pre_topc('#skF_4',A_219)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_231,c_491])).

tff(c_539,plain,(
    ! [D_226,A_227] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_226)) = k3_tmap_1(A_227,'#skF_2','#skF_4',D_226,'#skF_5')
      | ~ m1_pre_topc(D_226,'#skF_4')
      | ~ m1_pre_topc(D_226,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_504])).

tff(c_543,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_539])).

tff(c_552,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44,c_36,c_543])).

tff(c_553,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_552])).

tff(c_12,plain,(
    ! [A_10,C_14,B_13] :
      ( k9_relat_1(k7_relat_1(A_10,C_14),B_13) = k9_relat_1(A_10,B_13)
      | ~ r1_tarski(B_13,C_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_596,plain,(
    ! [B_13] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_13) = k9_relat_1('#skF_5',B_13)
      | ~ r1_tarski(B_13,u1_struct_0('#skF_3'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_12])).

tff(c_979,plain,(
    ! [B_278] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_278) = k9_relat_1('#skF_5',B_278)
      | ~ r1_tarski(B_278,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_596])).

tff(c_997,plain,(
    k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k9_relat_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_979])).

tff(c_341,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( m1_subset_1(k2_partfun1(A_196,B_197,C_198,D_199),k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_360,plain,(
    ! [D_170] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_170),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_341])).

tff(c_372,plain,(
    ! [D_200] : m1_subset_1(k7_relat_1('#skF_5',D_200),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_360])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_385,plain,(
    ! [D_200] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_200))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_372,c_6])).

tff(c_400,plain,(
    ! [D_200] : v1_relat_1(k7_relat_1('#skF_5',D_200)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_385])).

tff(c_134,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k7_relset_1(A_143,B_144,C_145,D_146) = k9_relat_1(C_145,D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,(
    ! [D_146] : k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_146) = k9_relat_1('#skF_5',D_146) ),
    inference(resolution,[status(thm)],[c_38,c_134])).

tff(c_182,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( m1_subset_1(k7_relset_1(A_161,B_162,C_163,D_164),k1_zfmisc_1(B_162))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_197,plain,(
    ! [D_146] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_146),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_182])).

tff(c_204,plain,(
    ! [D_165] : m1_subset_1(k9_relat_1('#skF_5',D_165),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_197])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_212,plain,(
    ! [D_165] : r1_tarski(k9_relat_1('#skF_5',D_165),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_244,plain,(
    ! [C_173,A_174,B_175] :
      ( m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ r1_tarski(k2_relat_1(C_173),B_175)
      | ~ r1_tarski(k1_relat_1(C_173),A_174)
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_622,plain,(
    ! [C_230,A_231,B_232] :
      ( r1_tarski(C_230,k2_zfmisc_1(A_231,B_232))
      | ~ r1_tarski(k2_relat_1(C_230),B_232)
      | ~ r1_tarski(k1_relat_1(C_230),A_231)
      | ~ v1_relat_1(C_230) ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_3116,plain,(
    ! [B_618,A_619,A_620,B_621] :
      ( r1_tarski(k7_relat_1(B_618,A_619),k2_zfmisc_1(A_620,B_621))
      | ~ r1_tarski(k9_relat_1(B_618,A_619),B_621)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_618,A_619)),A_620)
      | ~ v1_relat_1(k7_relat_1(B_618,A_619))
      | ~ v1_relat_1(B_618) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_622])).

tff(c_3140,plain,(
    ! [B_625,A_626,B_627] :
      ( r1_tarski(k7_relat_1(B_625,A_626),k2_zfmisc_1(A_626,B_627))
      | ~ r1_tarski(k9_relat_1(B_625,A_626),B_627)
      | ~ v1_relat_1(k7_relat_1(B_625,A_626))
      | ~ v1_relat_1(B_625) ) ),
    inference(resolution,[status(thm)],[c_14,c_3116])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_143,B_144,A_1,D_146] :
      ( k7_relset_1(A_143,B_144,A_1,D_146) = k9_relat_1(A_1,D_146)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_143,B_144)) ) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_3363,plain,(
    ! [A_649,B_650,B_651,D_652] :
      ( k7_relset_1(A_649,B_650,k7_relat_1(B_651,A_649),D_652) = k9_relat_1(k7_relat_1(B_651,A_649),D_652)
      | ~ r1_tarski(k9_relat_1(B_651,A_649),B_650)
      | ~ v1_relat_1(k7_relat_1(B_651,A_649))
      | ~ v1_relat_1(B_651) ) ),
    inference(resolution,[status(thm)],[c_3140,c_141])).

tff(c_3387,plain,(
    ! [D_165,D_652] :
      ( k7_relset_1(D_165,u1_struct_0('#skF_2'),k7_relat_1('#skF_5',D_165),D_652) = k9_relat_1(k7_relat_1('#skF_5',D_165),D_652)
      | ~ v1_relat_1(k7_relat_1('#skF_5',D_165))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_212,c_3363])).

tff(c_3420,plain,(
    ! [D_653,D_654] : k7_relset_1(D_653,u1_struct_0('#skF_2'),k7_relat_1('#skF_5',D_653),D_654) = k9_relat_1(k7_relat_1('#skF_5',D_653),D_654) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_400,c_3387])).

tff(c_3445,plain,(
    ! [D_654] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_654) = k9_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),D_654) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_3420])).

tff(c_3459,plain,(
    ! [D_654] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_654) = k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_654) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_3445])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_142,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_30])).

tff(c_3562,plain,(
    k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3459,c_142])).

tff(c_3565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_3562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.33  
% 6.45/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.33  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.45/2.33  
% 6.45/2.33  %Foreground sorts:
% 6.45/2.33  
% 6.45/2.33  
% 6.45/2.33  %Background operators:
% 6.45/2.33  
% 6.45/2.33  
% 6.45/2.33  %Foreground operators:
% 6.45/2.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.45/2.33  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.45/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.45/2.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.45/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.45/2.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.45/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.45/2.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.45/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.45/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.45/2.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.45/2.33  tff('#skF_3', type, '#skF_3': $i).
% 6.45/2.33  tff('#skF_1', type, '#skF_1': $i).
% 6.45/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.45/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.45/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.45/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.45/2.33  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.45/2.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.45/2.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.45/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.45/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.33  
% 6.45/2.35  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (r1_tarski(F, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k7_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tmap_1)).
% 6.45/2.35  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.45/2.35  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.45/2.35  tff(f_83, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.45/2.35  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 6.45/2.35  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 6.45/2.35  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.45/2.35  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.45/2.35  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 6.45/2.35  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.45/2.35  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 6.45/2.35  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.45/2.35  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 6.45/2.35  tff(c_32, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.45/2.35  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_79, plain, (![B_132, A_133]: (v1_relat_1(B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.45/2.35  tff(c_82, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_38, c_79])).
% 6.45/2.35  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_82])).
% 6.45/2.35  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_219, plain, (![A_167, B_168, C_169, D_170]: (k2_partfun1(A_167, B_168, C_169, D_170)=k7_relat_1(C_169, D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_funct_1(C_169))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.45/2.35  tff(c_224, plain, (![D_170]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_170)=k7_relat_1('#skF_5', D_170) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_219])).
% 6.45/2.35  tff(c_231, plain, (![D_170]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_170)=k7_relat_1('#skF_5', D_170))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_224])).
% 6.45/2.35  tff(c_478, plain, (![D_220, C_221, E_218, B_217, A_219]: (k3_tmap_1(A_219, B_217, C_221, D_220, E_218)=k2_partfun1(u1_struct_0(C_221), u1_struct_0(B_217), E_218, u1_struct_0(D_220)) | ~m1_pre_topc(D_220, C_221) | ~m1_subset_1(E_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_221), u1_struct_0(B_217)))) | ~v1_funct_2(E_218, u1_struct_0(C_221), u1_struct_0(B_217)) | ~v1_funct_1(E_218) | ~m1_pre_topc(D_220, A_219) | ~m1_pre_topc(C_221, A_219) | ~l1_pre_topc(B_217) | ~v2_pre_topc(B_217) | v2_struct_0(B_217) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.45/2.35  tff(c_491, plain, (![A_219, D_220]: (k3_tmap_1(A_219, '#skF_2', '#skF_4', D_220, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_220)) | ~m1_pre_topc(D_220, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_220, A_219) | ~m1_pre_topc('#skF_4', A_219) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(resolution, [status(thm)], [c_38, c_478])).
% 6.45/2.35  tff(c_504, plain, (![D_220, A_219]: (k7_relat_1('#skF_5', u1_struct_0(D_220))=k3_tmap_1(A_219, '#skF_2', '#skF_4', D_220, '#skF_5') | ~m1_pre_topc(D_220, '#skF_4') | ~m1_pre_topc(D_220, A_219) | ~m1_pre_topc('#skF_4', A_219) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_40, c_231, c_491])).
% 6.45/2.35  tff(c_539, plain, (![D_226, A_227]: (k7_relat_1('#skF_5', u1_struct_0(D_226))=k3_tmap_1(A_227, '#skF_2', '#skF_4', D_226, '#skF_5') | ~m1_pre_topc(D_226, '#skF_4') | ~m1_pre_topc(D_226, A_227) | ~m1_pre_topc('#skF_4', A_227) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(negUnitSimplification, [status(thm)], [c_56, c_504])).
% 6.45/2.35  tff(c_543, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_539])).
% 6.45/2.35  tff(c_552, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44, c_36, c_543])).
% 6.45/2.35  tff(c_553, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_552])).
% 6.45/2.35  tff(c_12, plain, (![A_10, C_14, B_13]: (k9_relat_1(k7_relat_1(A_10, C_14), B_13)=k9_relat_1(A_10, B_13) | ~r1_tarski(B_13, C_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.45/2.35  tff(c_596, plain, (![B_13]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_13)=k9_relat_1('#skF_5', B_13) | ~r1_tarski(B_13, u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_12])).
% 6.45/2.35  tff(c_979, plain, (![B_278]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_278)=k9_relat_1('#skF_5', B_278) | ~r1_tarski(B_278, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_596])).
% 6.45/2.35  tff(c_997, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_979])).
% 6.45/2.35  tff(c_341, plain, (![A_196, B_197, C_198, D_199]: (m1_subset_1(k2_partfun1(A_196, B_197, C_198, D_199), k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(C_198))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.45/2.35  tff(c_360, plain, (![D_170]: (m1_subset_1(k7_relat_1('#skF_5', D_170), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_341])).
% 6.45/2.35  tff(c_372, plain, (![D_200]: (m1_subset_1(k7_relat_1('#skF_5', D_200), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_360])).
% 6.45/2.35  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.45/2.35  tff(c_385, plain, (![D_200]: (v1_relat_1(k7_relat_1('#skF_5', D_200)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_372, c_6])).
% 6.45/2.35  tff(c_400, plain, (![D_200]: (v1_relat_1(k7_relat_1('#skF_5', D_200)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_385])).
% 6.45/2.35  tff(c_134, plain, (![A_143, B_144, C_145, D_146]: (k7_relset_1(A_143, B_144, C_145, D_146)=k9_relat_1(C_145, D_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.45/2.35  tff(c_140, plain, (![D_146]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_146)=k9_relat_1('#skF_5', D_146))), inference(resolution, [status(thm)], [c_38, c_134])).
% 6.45/2.35  tff(c_182, plain, (![A_161, B_162, C_163, D_164]: (m1_subset_1(k7_relset_1(A_161, B_162, C_163, D_164), k1_zfmisc_1(B_162)) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.45/2.35  tff(c_197, plain, (![D_146]: (m1_subset_1(k9_relat_1('#skF_5', D_146), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_140, c_182])).
% 6.45/2.35  tff(c_204, plain, (![D_165]: (m1_subset_1(k9_relat_1('#skF_5', D_165), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_197])).
% 6.45/2.35  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.45/2.35  tff(c_212, plain, (![D_165]: (r1_tarski(k9_relat_1('#skF_5', D_165), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_204, c_2])).
% 6.45/2.35  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.45/2.35  tff(c_10, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.45/2.35  tff(c_244, plain, (![C_173, A_174, B_175]: (m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~r1_tarski(k2_relat_1(C_173), B_175) | ~r1_tarski(k1_relat_1(C_173), A_174) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.45/2.35  tff(c_622, plain, (![C_230, A_231, B_232]: (r1_tarski(C_230, k2_zfmisc_1(A_231, B_232)) | ~r1_tarski(k2_relat_1(C_230), B_232) | ~r1_tarski(k1_relat_1(C_230), A_231) | ~v1_relat_1(C_230))), inference(resolution, [status(thm)], [c_244, c_2])).
% 6.45/2.35  tff(c_3116, plain, (![B_618, A_619, A_620, B_621]: (r1_tarski(k7_relat_1(B_618, A_619), k2_zfmisc_1(A_620, B_621)) | ~r1_tarski(k9_relat_1(B_618, A_619), B_621) | ~r1_tarski(k1_relat_1(k7_relat_1(B_618, A_619)), A_620) | ~v1_relat_1(k7_relat_1(B_618, A_619)) | ~v1_relat_1(B_618))), inference(superposition, [status(thm), theory('equality')], [c_10, c_622])).
% 6.45/2.35  tff(c_3140, plain, (![B_625, A_626, B_627]: (r1_tarski(k7_relat_1(B_625, A_626), k2_zfmisc_1(A_626, B_627)) | ~r1_tarski(k9_relat_1(B_625, A_626), B_627) | ~v1_relat_1(k7_relat_1(B_625, A_626)) | ~v1_relat_1(B_625))), inference(resolution, [status(thm)], [c_14, c_3116])).
% 6.45/2.35  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.45/2.35  tff(c_141, plain, (![A_143, B_144, A_1, D_146]: (k7_relset_1(A_143, B_144, A_1, D_146)=k9_relat_1(A_1, D_146) | ~r1_tarski(A_1, k2_zfmisc_1(A_143, B_144)))), inference(resolution, [status(thm)], [c_4, c_134])).
% 6.45/2.35  tff(c_3363, plain, (![A_649, B_650, B_651, D_652]: (k7_relset_1(A_649, B_650, k7_relat_1(B_651, A_649), D_652)=k9_relat_1(k7_relat_1(B_651, A_649), D_652) | ~r1_tarski(k9_relat_1(B_651, A_649), B_650) | ~v1_relat_1(k7_relat_1(B_651, A_649)) | ~v1_relat_1(B_651))), inference(resolution, [status(thm)], [c_3140, c_141])).
% 6.45/2.35  tff(c_3387, plain, (![D_165, D_652]: (k7_relset_1(D_165, u1_struct_0('#skF_2'), k7_relat_1('#skF_5', D_165), D_652)=k9_relat_1(k7_relat_1('#skF_5', D_165), D_652) | ~v1_relat_1(k7_relat_1('#skF_5', D_165)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_212, c_3363])).
% 6.45/2.35  tff(c_3420, plain, (![D_653, D_654]: (k7_relset_1(D_653, u1_struct_0('#skF_2'), k7_relat_1('#skF_5', D_653), D_654)=k9_relat_1(k7_relat_1('#skF_5', D_653), D_654))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_400, c_3387])).
% 6.45/2.35  tff(c_3445, plain, (![D_654]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_654)=k9_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), D_654))), inference(superposition, [status(thm), theory('equality')], [c_553, c_3420])).
% 6.45/2.35  tff(c_3459, plain, (![D_654]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_654)=k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_654))), inference(demodulation, [status(thm), theory('equality')], [c_553, c_3445])).
% 6.45/2.35  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.35  tff(c_142, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_30])).
% 6.45/2.35  tff(c_3562, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3459, c_142])).
% 6.45/2.35  tff(c_3565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_997, c_3562])).
% 6.45/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.35  
% 6.45/2.35  Inference rules
% 6.45/2.35  ----------------------
% 6.45/2.35  #Ref     : 0
% 6.45/2.35  #Sup     : 756
% 6.45/2.35  #Fact    : 0
% 6.45/2.35  #Define  : 0
% 6.45/2.35  #Split   : 5
% 6.45/2.35  #Chain   : 0
% 6.45/2.35  #Close   : 0
% 6.45/2.35  
% 6.45/2.35  Ordering : KBO
% 6.45/2.35  
% 6.45/2.35  Simplification rules
% 6.45/2.35  ----------------------
% 6.45/2.35  #Subsume      : 102
% 6.45/2.35  #Demod        : 978
% 6.45/2.35  #Tautology    : 211
% 6.45/2.35  #SimpNegUnit  : 58
% 6.45/2.35  #BackRed      : 20
% 6.45/2.35  
% 6.45/2.35  #Partial instantiations: 0
% 6.45/2.35  #Strategies tried      : 1
% 6.45/2.35  
% 6.45/2.35  Timing (in seconds)
% 6.45/2.35  ----------------------
% 6.45/2.35  Preprocessing        : 0.36
% 6.45/2.35  Parsing              : 0.19
% 6.45/2.35  CNF conversion       : 0.03
% 6.45/2.35  Main loop            : 1.16
% 6.45/2.35  Inferencing          : 0.40
% 6.45/2.35  Reduction            : 0.45
% 6.45/2.35  Demodulation         : 0.34
% 6.45/2.35  BG Simplification    : 0.05
% 6.45/2.35  Subsumption          : 0.19
% 6.45/2.35  Abstraction          : 0.07
% 6.45/2.35  MUC search           : 0.00
% 6.45/2.35  Cooper               : 0.00
% 6.45/2.35  Total                : 1.56
% 6.45/2.35  Index Insertion      : 0.00
% 6.45/2.35  Index Deletion       : 0.00
% 6.45/2.35  Index Matching       : 0.00
% 6.45/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
