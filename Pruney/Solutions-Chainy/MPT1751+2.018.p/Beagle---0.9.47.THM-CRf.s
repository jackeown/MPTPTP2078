%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:00 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 292 expanded)
%              Number of leaves         :   40 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 (1403 expanded)
%              Number of equality atoms :   37 ( 149 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_73,plain,(
    ! [B_85,A_86] :
      ( v1_relat_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_251,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k2_partfun1(A_129,B_130,C_131,D_132) = k7_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_256,plain,(
    ! [D_132] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_132) = k7_relat_1('#skF_4',D_132)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_251])).

tff(c_263,plain,(
    ! [D_132] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_132) = k7_relat_1('#skF_4',D_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_256])).

tff(c_483,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k2_partfun1(u1_struct_0(A_178),u1_struct_0(B_179),C_180,u1_struct_0(D_181)) = k2_tmap_1(A_178,B_179,C_180,D_181)
      | ~ m1_pre_topc(D_181,A_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178),u1_struct_0(B_179))))
      | ~ v1_funct_2(C_180,u1_struct_0(A_178),u1_struct_0(B_179))
      | ~ v1_funct_1(C_180)
      | ~ l1_pre_topc(B_179)
      | ~ v2_pre_topc(B_179)
      | v2_struct_0(B_179)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_496,plain,(
    ! [D_181] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_181)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_181)
      | ~ m1_pre_topc(D_181,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_483])).

tff(c_509,plain,(
    ! [D_181] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_181)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_181)
      | ~ m1_pre_topc(D_181,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_40,c_38,c_263,c_496])).

tff(c_512,plain,(
    ! [D_182] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_182)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_182)
      | ~ m1_pre_topc(D_182,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_509])).

tff(c_12,plain,(
    ! [A_10,C_14,B_13] :
      ( k9_relat_1(k7_relat_1(A_10,C_14),B_13) = k9_relat_1(A_10,B_13)
      | ~ r1_tarski(B_13,C_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_532,plain,(
    ! [D_182,B_13] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_182),B_13) = k9_relat_1('#skF_4',B_13)
      | ~ r1_tarski(B_13,u1_struct_0(D_182))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_182,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_12])).

tff(c_964,plain,(
    ! [D_252,B_253] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_252),B_253) = k9_relat_1('#skF_4',B_253)
      | ~ r1_tarski(B_253,u1_struct_0(D_252))
      | ~ m1_pre_topc(D_252,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_532])).

tff(c_996,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_964])).

tff(c_1008,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_996])).

tff(c_346,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( m1_subset_1(k2_partfun1(A_157,B_158,C_159,D_160),k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_365,plain,(
    ! [D_132] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_132),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_346])).

tff(c_376,plain,(
    ! [D_132] : m1_subset_1(k7_relat_1('#skF_4',D_132),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_365])).

tff(c_899,plain,(
    ! [D_241] :
      ( m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_241),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(D_241,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_376])).

tff(c_18,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( k7_relset_1(A_21,B_22,C_23,D_24) = k9_relat_1(C_23,D_24)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2014,plain,(
    ! [D_445,D_446] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_445),D_446) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_445),D_446)
      | ~ m1_pre_topc(D_445,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_899,c_18])).

tff(c_510,plain,(
    ! [D_181] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_181)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_181)
      | ~ m1_pre_topc(D_181,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_509])).

tff(c_377,plain,(
    ! [D_161] : m1_subset_1(k7_relat_1('#skF_4',D_161),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_365])).

tff(c_794,plain,(
    ! [D_223,D_224] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_223),D_224) = k9_relat_1(k7_relat_1('#skF_4',D_223),D_224) ),
    inference(resolution,[status(thm)],[c_377,c_18])).

tff(c_809,plain,(
    ! [D_181,D_224] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_181),D_224) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_181)),D_224)
      | ~ m1_pre_topc(D_181,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_794])).

tff(c_2020,plain,(
    ! [D_445,D_446] :
      ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_445)),D_446) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_445),D_446)
      | ~ m1_pre_topc(D_445,'#skF_2')
      | ~ m1_pre_topc(D_445,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_809])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_390,plain,(
    ! [D_161] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_161))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_377,c_6])).

tff(c_405,plain,(
    ! [D_161] : v1_relat_1(k7_relat_1('#skF_4',D_161)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_390])).

tff(c_189,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k7_relset_1(A_118,B_119,C_120,D_121) = k9_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_199,plain,(
    ! [D_121] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_121) = k9_relat_1('#skF_4',D_121) ),
    inference(resolution,[status(thm)],[c_36,c_189])).

tff(c_128,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( m1_subset_1(k7_relset_1(A_96,B_97,C_98,D_99),k1_zfmisc_1(B_97))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r1_tarski(k7_relset_1(A_100,B_101,C_102,D_103),B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_147,plain,(
    ! [D_103] : r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_103),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_137])).

tff(c_201,plain,(
    ! [D_103] : r1_tarski(k9_relat_1('#skF_4',D_103),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_147])).

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

tff(c_317,plain,(
    ! [C_151,A_152,B_153] :
      ( m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ r1_tarski(k2_relat_1(C_151),B_153)
      | ~ r1_tarski(k1_relat_1(C_151),A_152)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_343,plain,(
    ! [C_154,A_155,B_156] :
      ( r1_tarski(C_154,k2_zfmisc_1(A_155,B_156))
      | ~ r1_tarski(k2_relat_1(C_154),B_156)
      | ~ r1_tarski(k1_relat_1(C_154),A_155)
      | ~ v1_relat_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_3342,plain,(
    ! [B_646,A_647,A_648,B_649] :
      ( r1_tarski(k7_relat_1(B_646,A_647),k2_zfmisc_1(A_648,B_649))
      | ~ r1_tarski(k9_relat_1(B_646,A_647),B_649)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_646,A_647)),A_648)
      | ~ v1_relat_1(k7_relat_1(B_646,A_647))
      | ~ v1_relat_1(B_646) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_343])).

tff(c_3350,plain,(
    ! [B_650,A_651,B_652] :
      ( r1_tarski(k7_relat_1(B_650,A_651),k2_zfmisc_1(A_651,B_652))
      | ~ r1_tarski(k9_relat_1(B_650,A_651),B_652)
      | ~ v1_relat_1(k7_relat_1(B_650,A_651))
      | ~ v1_relat_1(B_650) ) ),
    inference(resolution,[status(thm)],[c_14,c_3342])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [A_118,B_119,A_1,D_121] :
      ( k7_relset_1(A_118,B_119,A_1,D_121) = k9_relat_1(A_1,D_121)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_118,B_119)) ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_3515,plain,(
    ! [A_669,B_670,B_671,D_672] :
      ( k7_relset_1(A_669,B_670,k7_relat_1(B_671,A_669),D_672) = k9_relat_1(k7_relat_1(B_671,A_669),D_672)
      | ~ r1_tarski(k9_relat_1(B_671,A_669),B_670)
      | ~ v1_relat_1(k7_relat_1(B_671,A_669))
      | ~ v1_relat_1(B_671) ) ),
    inference(resolution,[status(thm)],[c_3350,c_200])).

tff(c_3545,plain,(
    ! [D_103,D_672] :
      ( k7_relset_1(D_103,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_103),D_672) = k9_relat_1(k7_relat_1('#skF_4',D_103),D_672)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_103))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_201,c_3515])).

tff(c_3570,plain,(
    ! [D_673,D_674] : k7_relset_1(D_673,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_673),D_674) = k9_relat_1(k7_relat_1('#skF_4',D_673),D_674) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_405,c_3545])).

tff(c_3653,plain,(
    ! [D_682,D_683] :
      ( k7_relset_1(u1_struct_0(D_682),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_682),D_683) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_682)),D_683)
      | ~ m1_pre_topc(D_682,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_3570])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_202,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_30])).

tff(c_3677,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3653,c_202])).

tff(c_3701,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3677])).

tff(c_3707,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2020,c_3701])).

tff(c_3716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_1008,c_3707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.26  
% 6.39/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.26  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.39/2.26  
% 6.39/2.26  %Foreground sorts:
% 6.39/2.26  
% 6.39/2.26  
% 6.39/2.26  %Background operators:
% 6.39/2.26  
% 6.39/2.26  
% 6.39/2.26  %Foreground operators:
% 6.39/2.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.39/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.39/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.39/2.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.39/2.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.39/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.39/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.39/2.26  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.39/2.26  tff('#skF_5', type, '#skF_5': $i).
% 6.39/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.39/2.26  tff('#skF_2', type, '#skF_2': $i).
% 6.39/2.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.39/2.26  tff('#skF_3', type, '#skF_3': $i).
% 6.39/2.26  tff('#skF_1', type, '#skF_1': $i).
% 6.39/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.39/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.39/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.39/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.39/2.26  tff('#skF_4', type, '#skF_4': $i).
% 6.39/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.39/2.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.39/2.26  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.39/2.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.39/2.26  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.39/2.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.39/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.39/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.39/2.26  
% 6.39/2.28  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 6.39/2.28  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.39/2.28  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.39/2.28  tff(f_83, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.39/2.28  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.39/2.28  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 6.39/2.28  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.39/2.28  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.39/2.28  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 6.39/2.28  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.39/2.28  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 6.39/2.28  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.39/2.28  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.39/2.28  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_32, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.39/2.28  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_73, plain, (![B_85, A_86]: (v1_relat_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.39/2.28  tff(c_76, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_73])).
% 6.39/2.28  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_76])).
% 6.39/2.28  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_251, plain, (![A_129, B_130, C_131, D_132]: (k2_partfun1(A_129, B_130, C_131, D_132)=k7_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.39/2.28  tff(c_256, plain, (![D_132]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_132)=k7_relat_1('#skF_4', D_132) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_251])).
% 6.39/2.28  tff(c_263, plain, (![D_132]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_132)=k7_relat_1('#skF_4', D_132))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_256])).
% 6.39/2.28  tff(c_483, plain, (![A_178, B_179, C_180, D_181]: (k2_partfun1(u1_struct_0(A_178), u1_struct_0(B_179), C_180, u1_struct_0(D_181))=k2_tmap_1(A_178, B_179, C_180, D_181) | ~m1_pre_topc(D_181, A_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178), u1_struct_0(B_179)))) | ~v1_funct_2(C_180, u1_struct_0(A_178), u1_struct_0(B_179)) | ~v1_funct_1(C_180) | ~l1_pre_topc(B_179) | ~v2_pre_topc(B_179) | v2_struct_0(B_179) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.39/2.28  tff(c_496, plain, (![D_181]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_181))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_181) | ~m1_pre_topc(D_181, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_483])).
% 6.39/2.28  tff(c_509, plain, (![D_181]: (k7_relat_1('#skF_4', u1_struct_0(D_181))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_181) | ~m1_pre_topc(D_181, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_40, c_38, c_263, c_496])).
% 6.39/2.28  tff(c_512, plain, (![D_182]: (k7_relat_1('#skF_4', u1_struct_0(D_182))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_182) | ~m1_pre_topc(D_182, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_509])).
% 6.39/2.28  tff(c_12, plain, (![A_10, C_14, B_13]: (k9_relat_1(k7_relat_1(A_10, C_14), B_13)=k9_relat_1(A_10, B_13) | ~r1_tarski(B_13, C_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.39/2.28  tff(c_532, plain, (![D_182, B_13]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_182), B_13)=k9_relat_1('#skF_4', B_13) | ~r1_tarski(B_13, u1_struct_0(D_182)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_182, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_512, c_12])).
% 6.39/2.28  tff(c_964, plain, (![D_252, B_253]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_252), B_253)=k9_relat_1('#skF_4', B_253) | ~r1_tarski(B_253, u1_struct_0(D_252)) | ~m1_pre_topc(D_252, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_532])).
% 6.39/2.28  tff(c_996, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_964])).
% 6.39/2.28  tff(c_1008, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_996])).
% 6.39/2.28  tff(c_346, plain, (![A_157, B_158, C_159, D_160]: (m1_subset_1(k2_partfun1(A_157, B_158, C_159, D_160), k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.39/2.28  tff(c_365, plain, (![D_132]: (m1_subset_1(k7_relat_1('#skF_4', D_132), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_346])).
% 6.39/2.28  tff(c_376, plain, (![D_132]: (m1_subset_1(k7_relat_1('#skF_4', D_132), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_365])).
% 6.39/2.28  tff(c_899, plain, (![D_241]: (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_241), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~m1_pre_topc(D_241, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_512, c_376])).
% 6.39/2.28  tff(c_18, plain, (![A_21, B_22, C_23, D_24]: (k7_relset_1(A_21, B_22, C_23, D_24)=k9_relat_1(C_23, D_24) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.39/2.28  tff(c_2014, plain, (![D_445, D_446]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_445), D_446)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_445), D_446) | ~m1_pre_topc(D_445, '#skF_2'))), inference(resolution, [status(thm)], [c_899, c_18])).
% 6.39/2.28  tff(c_510, plain, (![D_181]: (k7_relat_1('#skF_4', u1_struct_0(D_181))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_181) | ~m1_pre_topc(D_181, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_509])).
% 6.39/2.28  tff(c_377, plain, (![D_161]: (m1_subset_1(k7_relat_1('#skF_4', D_161), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_365])).
% 6.39/2.28  tff(c_794, plain, (![D_223, D_224]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_223), D_224)=k9_relat_1(k7_relat_1('#skF_4', D_223), D_224))), inference(resolution, [status(thm)], [c_377, c_18])).
% 6.39/2.28  tff(c_809, plain, (![D_181, D_224]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_181), D_224)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_181)), D_224) | ~m1_pre_topc(D_181, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_510, c_794])).
% 6.39/2.28  tff(c_2020, plain, (![D_445, D_446]: (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_445)), D_446)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_445), D_446) | ~m1_pre_topc(D_445, '#skF_2') | ~m1_pre_topc(D_445, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_809])).
% 6.39/2.28  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.39/2.28  tff(c_390, plain, (![D_161]: (v1_relat_1(k7_relat_1('#skF_4', D_161)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_377, c_6])).
% 6.39/2.28  tff(c_405, plain, (![D_161]: (v1_relat_1(k7_relat_1('#skF_4', D_161)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_390])).
% 6.39/2.28  tff(c_189, plain, (![A_118, B_119, C_120, D_121]: (k7_relset_1(A_118, B_119, C_120, D_121)=k9_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.39/2.28  tff(c_199, plain, (![D_121]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_121)=k9_relat_1('#skF_4', D_121))), inference(resolution, [status(thm)], [c_36, c_189])).
% 6.39/2.28  tff(c_128, plain, (![A_96, B_97, C_98, D_99]: (m1_subset_1(k7_relset_1(A_96, B_97, C_98, D_99), k1_zfmisc_1(B_97)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.39/2.28  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.39/2.28  tff(c_137, plain, (![A_100, B_101, C_102, D_103]: (r1_tarski(k7_relset_1(A_100, B_101, C_102, D_103), B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(resolution, [status(thm)], [c_128, c_2])).
% 6.39/2.28  tff(c_147, plain, (![D_103]: (r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_103), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_137])).
% 6.39/2.28  tff(c_201, plain, (![D_103]: (r1_tarski(k9_relat_1('#skF_4', D_103), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_147])).
% 6.39/2.28  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.28  tff(c_10, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.39/2.28  tff(c_317, plain, (![C_151, A_152, B_153]: (m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~r1_tarski(k2_relat_1(C_151), B_153) | ~r1_tarski(k1_relat_1(C_151), A_152) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.39/2.28  tff(c_343, plain, (![C_154, A_155, B_156]: (r1_tarski(C_154, k2_zfmisc_1(A_155, B_156)) | ~r1_tarski(k2_relat_1(C_154), B_156) | ~r1_tarski(k1_relat_1(C_154), A_155) | ~v1_relat_1(C_154))), inference(resolution, [status(thm)], [c_317, c_2])).
% 6.39/2.28  tff(c_3342, plain, (![B_646, A_647, A_648, B_649]: (r1_tarski(k7_relat_1(B_646, A_647), k2_zfmisc_1(A_648, B_649)) | ~r1_tarski(k9_relat_1(B_646, A_647), B_649) | ~r1_tarski(k1_relat_1(k7_relat_1(B_646, A_647)), A_648) | ~v1_relat_1(k7_relat_1(B_646, A_647)) | ~v1_relat_1(B_646))), inference(superposition, [status(thm), theory('equality')], [c_10, c_343])).
% 6.39/2.28  tff(c_3350, plain, (![B_650, A_651, B_652]: (r1_tarski(k7_relat_1(B_650, A_651), k2_zfmisc_1(A_651, B_652)) | ~r1_tarski(k9_relat_1(B_650, A_651), B_652) | ~v1_relat_1(k7_relat_1(B_650, A_651)) | ~v1_relat_1(B_650))), inference(resolution, [status(thm)], [c_14, c_3342])).
% 6.39/2.28  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.39/2.28  tff(c_200, plain, (![A_118, B_119, A_1, D_121]: (k7_relset_1(A_118, B_119, A_1, D_121)=k9_relat_1(A_1, D_121) | ~r1_tarski(A_1, k2_zfmisc_1(A_118, B_119)))), inference(resolution, [status(thm)], [c_4, c_189])).
% 6.39/2.28  tff(c_3515, plain, (![A_669, B_670, B_671, D_672]: (k7_relset_1(A_669, B_670, k7_relat_1(B_671, A_669), D_672)=k9_relat_1(k7_relat_1(B_671, A_669), D_672) | ~r1_tarski(k9_relat_1(B_671, A_669), B_670) | ~v1_relat_1(k7_relat_1(B_671, A_669)) | ~v1_relat_1(B_671))), inference(resolution, [status(thm)], [c_3350, c_200])).
% 6.39/2.28  tff(c_3545, plain, (![D_103, D_672]: (k7_relset_1(D_103, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_103), D_672)=k9_relat_1(k7_relat_1('#skF_4', D_103), D_672) | ~v1_relat_1(k7_relat_1('#skF_4', D_103)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_201, c_3515])).
% 6.39/2.28  tff(c_3570, plain, (![D_673, D_674]: (k7_relset_1(D_673, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_673), D_674)=k9_relat_1(k7_relat_1('#skF_4', D_673), D_674))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_405, c_3545])).
% 6.39/2.28  tff(c_3653, plain, (![D_682, D_683]: (k7_relset_1(u1_struct_0(D_682), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_682), D_683)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_682)), D_683) | ~m1_pre_topc(D_682, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_510, c_3570])).
% 6.39/2.28  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.39/2.28  tff(c_202, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_30])).
% 6.39/2.28  tff(c_3677, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3653, c_202])).
% 6.39/2.28  tff(c_3701, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3677])).
% 6.39/2.28  tff(c_3707, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2020, c_3701])).
% 6.39/2.28  tff(c_3716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_1008, c_3707])).
% 6.39/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.28  
% 6.39/2.28  Inference rules
% 6.39/2.28  ----------------------
% 6.39/2.28  #Ref     : 0
% 6.39/2.28  #Sup     : 848
% 6.39/2.28  #Fact    : 0
% 6.39/2.28  #Define  : 0
% 6.39/2.28  #Split   : 5
% 6.39/2.28  #Chain   : 0
% 6.39/2.28  #Close   : 0
% 6.39/2.28  
% 6.39/2.28  Ordering : KBO
% 6.39/2.28  
% 6.39/2.28  Simplification rules
% 6.39/2.28  ----------------------
% 6.39/2.28  #Subsume      : 162
% 6.39/2.28  #Demod        : 861
% 6.39/2.28  #Tautology    : 201
% 6.39/2.28  #SimpNegUnit  : 70
% 6.39/2.28  #BackRed      : 17
% 6.39/2.28  
% 6.39/2.28  #Partial instantiations: 0
% 6.39/2.28  #Strategies tried      : 1
% 6.39/2.28  
% 6.39/2.28  Timing (in seconds)
% 6.39/2.28  ----------------------
% 6.39/2.29  Preprocessing        : 0.36
% 6.39/2.29  Parsing              : 0.19
% 6.39/2.29  CNF conversion       : 0.03
% 6.39/2.29  Main loop            : 1.17
% 6.39/2.29  Inferencing          : 0.43
% 6.39/2.29  Reduction            : 0.42
% 6.39/2.29  Demodulation         : 0.31
% 6.39/2.29  BG Simplification    : 0.05
% 6.39/2.29  Subsumption          : 0.19
% 6.39/2.29  Abstraction          : 0.07
% 6.39/2.29  MUC search           : 0.00
% 6.39/2.29  Cooper               : 0.00
% 6.39/2.29  Total                : 1.56
% 6.39/2.29  Index Insertion      : 0.00
% 6.39/2.29  Index Deletion       : 0.00
% 6.39/2.29  Index Matching       : 0.00
% 6.39/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
