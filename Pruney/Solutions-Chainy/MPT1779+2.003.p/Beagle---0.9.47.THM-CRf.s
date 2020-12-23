%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:44 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 487 expanded)
%              Number of leaves         :   27 ( 207 expanded)
%              Depth                    :   14
%              Number of atoms          :  685 (5590 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   33 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_224,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(C,D)
                            & m1_pre_topc(E,C) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( ( v1_funct_1(k3_tmap_1(A,B,D,C,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,C,F),u1_struct_0(C),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,C,F),C,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,C,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                               => ( v1_funct_1(k3_tmap_1(A,B,D,E,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,E,F),u1_struct_0(E),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,E,F),E,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tmap_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_117,axiom,(
    ! [A] :
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
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(D,C)
                          & m1_pre_topc(E,D) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_163,axiom,(
    ! [A] :
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & v5_pre_topc(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
                          & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
                          & v5_pre_topc(k3_tmap_1(A,B,C,D,E),D,B)
                          & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_tmap_1)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_34,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_190,plain,(
    ! [D_205,E_209,B_206,C_207,A_208] :
      ( v1_funct_2(k3_tmap_1(A_208,B_206,C_207,D_205,E_209),u1_struct_0(D_205),u1_struct_0(B_206))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_207),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0(C_207),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | ~ m1_pre_topc(D_205,A_208)
      | ~ m1_pre_topc(C_207,A_208)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_196,plain,(
    ! [A_208,D_205] :
      ( v1_funct_2(k3_tmap_1(A_208,'#skF_2','#skF_4',D_205,'#skF_6'),u1_struct_0(D_205),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_205,A_208)
      | ~ m1_pre_topc('#skF_4',A_208)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_207,plain,(
    ! [A_208,D_205] :
      ( v1_funct_2(k3_tmap_1(A_208,'#skF_2','#skF_4',D_205,'#skF_6'),u1_struct_0(D_205),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_205,A_208)
      | ~ m1_pre_topc('#skF_4',A_208)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_196])).

tff(c_209,plain,(
    ! [A_210,D_211] :
      ( v1_funct_2(k3_tmap_1(A_210,'#skF_2','#skF_4',D_211,'#skF_6'),u1_struct_0(D_211),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_211,A_210)
      | ~ m1_pre_topc('#skF_4',A_210)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_207])).

tff(c_145,plain,(
    ! [E_197,B_194,C_195,D_193,A_196] :
      ( m1_subset_1(k3_tmap_1(A_196,B_194,C_195,D_193,E_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_193),u1_struct_0(B_194))))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_195),u1_struct_0(B_194))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_195),u1_struct_0(B_194))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc(D_193,A_196)
      | ~ m1_pre_topc(C_195,A_196)
      | ~ l1_pre_topc(B_194)
      | ~ v2_pre_topc(B_194)
      | v2_struct_0(B_194)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    ! [C_170,D_168,A_171,B_169,E_172] :
      ( v1_funct_1(k3_tmap_1(A_171,B_169,C_170,D_168,E_172))
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170),u1_struct_0(B_169))))
      | ~ v1_funct_2(E_172,u1_struct_0(C_170),u1_struct_0(B_169))
      | ~ v1_funct_1(E_172)
      | ~ m1_pre_topc(D_168,A_171)
      | ~ m1_pre_topc(C_170,A_171)
      | ~ l1_pre_topc(B_169)
      | ~ v2_pre_topc(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94,plain,(
    ! [A_171,D_168] :
      ( v1_funct_1(k3_tmap_1(A_171,'#skF_2','#skF_4',D_168,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_168,A_171)
      | ~ m1_pre_topc('#skF_4',A_171)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_101,plain,(
    ! [A_171,D_168] :
      ( v1_funct_1(k3_tmap_1(A_171,'#skF_2','#skF_4',D_168,'#skF_6'))
      | ~ m1_pre_topc(D_168,A_171)
      | ~ m1_pre_topc('#skF_4',A_171)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_94])).

tff(c_103,plain,(
    ! [A_173,D_174] :
      ( v1_funct_1(k3_tmap_1(A_173,'#skF_2','#skF_4',D_174,'#skF_6'))
      | ~ m1_pre_topc(D_174,A_173)
      | ~ m1_pre_topc('#skF_4',A_173)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_101])).

tff(c_22,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_89,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_106,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_103,c_89])).

tff(c_109,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_42,c_106])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_109])).

tff(c_112,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_114,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_152,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_145,c_114])).

tff(c_159,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_46,c_42,c_36,c_34,c_32,c_152])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_159])).

tff(c_162,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_169,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_212,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_209,c_169])).

tff(c_215,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_42,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_215])).

tff(c_218,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_30,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_26,plain,(
    v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_28,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_269,plain,(
    ! [D_228,C_230,E_232,A_231,B_229] :
      ( m1_subset_1(k3_tmap_1(A_231,B_229,C_230,D_228,E_232),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_228),u1_struct_0(B_229))))
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230),u1_struct_0(B_229))))
      | ~ v1_funct_2(E_232,u1_struct_0(C_230),u1_struct_0(B_229))
      | ~ v1_funct_1(E_232)
      | ~ m1_pre_topc(D_228,A_231)
      | ~ m1_pre_topc(C_230,A_231)
      | ~ l1_pre_topc(B_229)
      | ~ v2_pre_topc(B_229)
      | v2_struct_0(B_229)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] :
      ( v1_funct_2(k3_tmap_1(A_5,B_6,C_7,D_8,E_9),u1_struct_0(D_8),u1_struct_0(B_6))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0(B_6))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0(B_6))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc(D_8,A_5)
      | ~ m1_pre_topc(C_7,A_5)
      | ~ l1_pre_topc(B_6)
      | ~ v2_pre_topc(B_6)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_276,plain,(
    ! [D_228,D_8,C_230,A_5,E_232,A_231,B_229] :
      ( v1_funct_2(k3_tmap_1(A_5,B_229,D_228,D_8,k3_tmap_1(A_231,B_229,C_230,D_228,E_232)),u1_struct_0(D_8),u1_struct_0(B_229))
      | ~ v1_funct_2(k3_tmap_1(A_231,B_229,C_230,D_228,E_232),u1_struct_0(D_228),u1_struct_0(B_229))
      | ~ v1_funct_1(k3_tmap_1(A_231,B_229,C_230,D_228,E_232))
      | ~ m1_pre_topc(D_8,A_5)
      | ~ m1_pre_topc(D_228,A_5)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5)
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230),u1_struct_0(B_229))))
      | ~ v1_funct_2(E_232,u1_struct_0(C_230),u1_struct_0(B_229))
      | ~ v1_funct_1(E_232)
      | ~ m1_pre_topc(D_228,A_231)
      | ~ m1_pre_topc(C_230,A_231)
      | ~ l1_pre_topc(B_229)
      | ~ v2_pre_topc(B_229)
      | v2_struct_0(B_229)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_269,c_8])).

tff(c_250,plain,(
    ! [E_227,C_225,D_223,B_224,A_226] :
      ( v1_funct_2(k3_tmap_1(A_226,B_224,C_225,D_223,E_227),u1_struct_0(D_223),u1_struct_0(B_224))
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_225),u1_struct_0(B_224))))
      | ~ v1_funct_2(E_227,u1_struct_0(C_225),u1_struct_0(B_224))
      | ~ v1_funct_1(E_227)
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc(C_225,A_226)
      | ~ l1_pre_topc(B_224)
      | ~ v2_pre_topc(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_256,plain,(
    ! [A_226,D_223] :
      ( v1_funct_2(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'),u1_struct_0(D_223),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_32,c_250])).

tff(c_267,plain,(
    ! [A_226,D_223] :
      ( v1_funct_2(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'),u1_struct_0(D_223),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_256])).

tff(c_268,plain,(
    ! [A_226,D_223] :
      ( v1_funct_2(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'),u1_struct_0(D_223),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_267])).

tff(c_10,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] :
      ( v1_funct_1(k3_tmap_1(A_5,B_6,C_7,D_8,E_9))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0(B_6))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0(B_6))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc(D_8,A_5)
      | ~ m1_pre_topc(C_7,A_5)
      | ~ l1_pre_topc(B_6)
      | ~ v2_pre_topc(B_6)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_315,plain,(
    ! [D_257,A_260,E_263,B_262,D_261,C_258,A_259] :
      ( v1_funct_1(k3_tmap_1(A_260,B_262,D_261,D_257,k3_tmap_1(A_259,B_262,C_258,D_261,E_263)))
      | ~ v1_funct_2(k3_tmap_1(A_259,B_262,C_258,D_261,E_263),u1_struct_0(D_261),u1_struct_0(B_262))
      | ~ v1_funct_1(k3_tmap_1(A_259,B_262,C_258,D_261,E_263))
      | ~ m1_pre_topc(D_257,A_260)
      | ~ m1_pre_topc(D_261,A_260)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260)
      | ~ m1_subset_1(E_263,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_258),u1_struct_0(B_262))))
      | ~ v1_funct_2(E_263,u1_struct_0(C_258),u1_struct_0(B_262))
      | ~ v1_funct_1(E_263)
      | ~ m1_pre_topc(D_261,A_259)
      | ~ m1_pre_topc(C_258,A_259)
      | ~ l1_pre_topc(B_262)
      | ~ v2_pre_topc(B_262)
      | v2_struct_0(B_262)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_269,c_10])).

tff(c_321,plain,(
    ! [A_260,D_223,D_257,A_226] :
      ( v1_funct_1(k3_tmap_1(A_260,'#skF_2',D_223,D_257,k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6')))
      | ~ v1_funct_1(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'))
      | ~ m1_pre_topc(D_257,A_260)
      | ~ m1_pre_topc(D_223,A_260)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_268,c_315])).

tff(c_336,plain,(
    ! [A_260,D_223,D_257,A_226] :
      ( v1_funct_1(k3_tmap_1(A_260,'#skF_2',D_223,D_257,k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6')))
      | ~ v1_funct_1(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'))
      | ~ m1_pre_topc(D_257,A_260)
      | ~ m1_pre_topc(D_223,A_260)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_32,c_321])).

tff(c_337,plain,(
    ! [A_260,D_223,D_257,A_226] :
      ( v1_funct_1(k3_tmap_1(A_260,'#skF_2',D_223,D_257,k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6')))
      | ~ v1_funct_1(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'))
      | ~ m1_pre_topc(D_257,A_260)
      | ~ m1_pre_topc(D_223,A_260)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260)
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_336])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_24,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_113,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_219,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_163,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] :
      ( m1_subset_1(k3_tmap_1(A_5,B_6,C_7,D_8,E_9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8),u1_struct_0(B_6))))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0(B_6))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0(B_6))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc(D_8,A_5)
      | ~ m1_pre_topc(C_7,A_5)
      | ~ l1_pre_topc(B_6)
      | ~ v2_pre_topc(B_6)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_311,plain,(
    ! [E_255,D_256,B_254,A_253,F_252,C_251] :
      ( r2_funct_2(u1_struct_0(E_255),u1_struct_0(B_254),k3_tmap_1(A_253,B_254,D_256,E_255,k3_tmap_1(A_253,B_254,C_251,D_256,F_252)),k3_tmap_1(A_253,B_254,C_251,E_255,F_252))
      | ~ m1_subset_1(F_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251),u1_struct_0(B_254))))
      | ~ v1_funct_2(F_252,u1_struct_0(C_251),u1_struct_0(B_254))
      | ~ v1_funct_1(F_252)
      | ~ m1_pre_topc(E_255,D_256)
      | ~ m1_pre_topc(D_256,C_251)
      | ~ m1_pre_topc(E_255,A_253)
      | v2_struct_0(E_255)
      | ~ m1_pre_topc(D_256,A_253)
      | v2_struct_0(D_256)
      | ~ m1_pre_topc(C_251,A_253)
      | v2_struct_0(C_251)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_406,plain,(
    ! [D_313,A_314,B_312,C_311,F_315,E_316] :
      ( k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)) = k3_tmap_1(A_314,B_312,C_311,E_316,F_315)
      | ~ m1_subset_1(k3_tmap_1(A_314,B_312,C_311,E_316,F_315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_316),u1_struct_0(B_312))))
      | ~ v1_funct_2(k3_tmap_1(A_314,B_312,C_311,E_316,F_315),u1_struct_0(E_316),u1_struct_0(B_312))
      | ~ v1_funct_1(k3_tmap_1(A_314,B_312,C_311,E_316,F_315))
      | ~ m1_subset_1(k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_316),u1_struct_0(B_312))))
      | ~ v1_funct_2(k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)),u1_struct_0(E_316),u1_struct_0(B_312))
      | ~ v1_funct_1(k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)))
      | ~ m1_subset_1(F_315,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_311),u1_struct_0(B_312))))
      | ~ v1_funct_2(F_315,u1_struct_0(C_311),u1_struct_0(B_312))
      | ~ v1_funct_1(F_315)
      | ~ m1_pre_topc(E_316,D_313)
      | ~ m1_pre_topc(D_313,C_311)
      | ~ m1_pre_topc(E_316,A_314)
      | v2_struct_0(E_316)
      | ~ m1_pre_topc(D_313,A_314)
      | v2_struct_0(D_313)
      | ~ m1_pre_topc(C_311,A_314)
      | v2_struct_0(C_311)
      | ~ l1_pre_topc(B_312)
      | ~ v2_pre_topc(B_312)
      | v2_struct_0(B_312)
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(resolution,[status(thm)],[c_311,c_4])).

tff(c_490,plain,(
    ! [C_382,B_383,A_385,F_381,C_384,D_380] :
      ( k3_tmap_1(A_385,B_383,C_384,D_380,k3_tmap_1(A_385,B_383,C_382,C_384,F_381)) = k3_tmap_1(A_385,B_383,C_382,D_380,F_381)
      | ~ m1_subset_1(k3_tmap_1(A_385,B_383,C_382,D_380,F_381),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_380),u1_struct_0(B_383))))
      | ~ v1_funct_2(k3_tmap_1(A_385,B_383,C_382,D_380,F_381),u1_struct_0(D_380),u1_struct_0(B_383))
      | ~ v1_funct_1(k3_tmap_1(A_385,B_383,C_382,D_380,F_381))
      | ~ v1_funct_2(k3_tmap_1(A_385,B_383,C_384,D_380,k3_tmap_1(A_385,B_383,C_382,C_384,F_381)),u1_struct_0(D_380),u1_struct_0(B_383))
      | ~ v1_funct_1(k3_tmap_1(A_385,B_383,C_384,D_380,k3_tmap_1(A_385,B_383,C_382,C_384,F_381)))
      | ~ m1_subset_1(F_381,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_382),u1_struct_0(B_383))))
      | ~ v1_funct_2(F_381,u1_struct_0(C_382),u1_struct_0(B_383))
      | ~ v1_funct_1(F_381)
      | ~ m1_pre_topc(D_380,C_384)
      | ~ m1_pre_topc(C_384,C_382)
      | v2_struct_0(D_380)
      | v2_struct_0(C_384)
      | ~ m1_pre_topc(C_382,A_385)
      | v2_struct_0(C_382)
      | ~ m1_subset_1(k3_tmap_1(A_385,B_383,C_382,C_384,F_381),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384),u1_struct_0(B_383))))
      | ~ v1_funct_2(k3_tmap_1(A_385,B_383,C_382,C_384,F_381),u1_struct_0(C_384),u1_struct_0(B_383))
      | ~ v1_funct_1(k3_tmap_1(A_385,B_383,C_382,C_384,F_381))
      | ~ m1_pre_topc(D_380,A_385)
      | ~ m1_pre_topc(C_384,A_385)
      | ~ l1_pre_topc(B_383)
      | ~ v2_pre_topc(B_383)
      | v2_struct_0(B_383)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(resolution,[status(thm)],[c_6,c_406])).

tff(c_494,plain,(
    ! [C_384] :
      ( k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5',C_384)
      | ~ m1_pre_topc(C_384,'#skF_4')
      | v2_struct_0('#skF_5')
      | v2_struct_0(C_384)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),u1_struct_0(C_384),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ m1_pre_topc(C_384,'#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_163,c_490])).

tff(c_500,plain,(
    ! [C_384] :
      ( k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')))
      | ~ m1_pre_topc('#skF_5',C_384)
      | ~ m1_pre_topc(C_384,'#skF_4')
      | v2_struct_0('#skF_5')
      | v2_struct_0(C_384)
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),u1_struct_0(C_384),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'))
      | ~ m1_pre_topc(C_384,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_42,c_46,c_36,c_34,c_32,c_113,c_219,c_494])).

tff(c_506,plain,(
    ! [C_386] :
      ( k3_tmap_1('#skF_1','#skF_2',C_386,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',C_386,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',C_386,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6')))
      | ~ m1_pre_topc('#skF_5',C_386)
      | ~ m1_pre_topc(C_386,'#skF_4')
      | v2_struct_0(C_386)
      | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_386),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6'),u1_struct_0(C_386),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6'))
      | ~ m1_pre_topc(C_386,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_48,c_44,c_500])).

tff(c_516,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_506])).

tff(c_527,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30,c_28,c_40,c_38,c_516])).

tff(c_528,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_527])).

tff(c_529,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_528])).

tff(c_532,plain,
    ( ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_337,c_529])).

tff(c_538,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_50,c_42,c_30,c_532])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_538])).

tff(c_541,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_544,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_547,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_276,c_544])).

tff(c_553,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_46,c_50,c_36,c_34,c_32,c_42,c_30,c_28,c_547])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_553])).

tff(c_556,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_282,plain,(
    ! [E_239,A_243,B_242,D_241,C_240] :
      ( v5_pre_topc(k3_tmap_1(A_243,B_242,C_240,D_241,E_239),D_241,B_242)
      | ~ m1_pre_topc(D_241,C_240)
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240),u1_struct_0(B_242))))
      | ~ v5_pre_topc(E_239,C_240,B_242)
      | ~ v1_funct_2(E_239,u1_struct_0(C_240),u1_struct_0(B_242))
      | ~ v1_funct_1(E_239)
      | ~ m1_pre_topc(D_241,A_243)
      | v2_struct_0(D_241)
      | ~ m1_pre_topc(C_240,A_243)
      | v2_struct_0(C_240)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_353,plain,(
    ! [B_285,D_284,A_288,E_289,D_283,A_287,C_286] :
      ( v5_pre_topc(k3_tmap_1(A_288,B_285,D_283,D_284,k3_tmap_1(A_287,B_285,C_286,D_283,E_289)),D_284,B_285)
      | ~ m1_pre_topc(D_284,D_283)
      | ~ v5_pre_topc(k3_tmap_1(A_287,B_285,C_286,D_283,E_289),D_283,B_285)
      | ~ v1_funct_2(k3_tmap_1(A_287,B_285,C_286,D_283,E_289),u1_struct_0(D_283),u1_struct_0(B_285))
      | ~ v1_funct_1(k3_tmap_1(A_287,B_285,C_286,D_283,E_289))
      | ~ m1_pre_topc(D_284,A_288)
      | v2_struct_0(D_284)
      | ~ m1_pre_topc(D_283,A_288)
      | v2_struct_0(D_283)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288)
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_286),u1_struct_0(B_285))))
      | ~ v1_funct_2(E_289,u1_struct_0(C_286),u1_struct_0(B_285))
      | ~ v1_funct_1(E_289)
      | ~ m1_pre_topc(D_283,A_287)
      | ~ m1_pre_topc(C_286,A_287)
      | ~ l1_pre_topc(B_285)
      | ~ v2_pre_topc(B_285)
      | v2_struct_0(B_285)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(resolution,[status(thm)],[c_6,c_282])).

tff(c_361,plain,(
    ! [A_288,D_223,D_284,A_226] :
      ( v5_pre_topc(k3_tmap_1(A_288,'#skF_2',D_223,D_284,k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6')),D_284,'#skF_2')
      | ~ m1_pre_topc(D_284,D_223)
      | ~ v5_pre_topc(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'),D_223,'#skF_2')
      | ~ v1_funct_1(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'))
      | ~ m1_pre_topc(D_284,A_288)
      | v2_struct_0(D_284)
      | ~ m1_pre_topc(D_223,A_288)
      | v2_struct_0(D_223)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_268,c_353])).

tff(c_377,plain,(
    ! [A_288,D_223,D_284,A_226] :
      ( v5_pre_topc(k3_tmap_1(A_288,'#skF_2',D_223,D_284,k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6')),D_284,'#skF_2')
      | ~ m1_pre_topc(D_284,D_223)
      | ~ v5_pre_topc(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'),D_223,'#skF_2')
      | ~ v1_funct_1(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'))
      | ~ m1_pre_topc(D_284,A_288)
      | v2_struct_0(D_284)
      | ~ m1_pre_topc(D_223,A_288)
      | v2_struct_0(D_223)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_32,c_361])).

tff(c_378,plain,(
    ! [A_288,D_223,D_284,A_226] :
      ( v5_pre_topc(k3_tmap_1(A_288,'#skF_2',D_223,D_284,k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6')),D_284,'#skF_2')
      | ~ m1_pre_topc(D_284,D_223)
      | ~ v5_pre_topc(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'),D_223,'#skF_2')
      | ~ v1_funct_1(k3_tmap_1(A_226,'#skF_2','#skF_4',D_223,'#skF_6'))
      | ~ m1_pre_topc(D_284,A_288)
      | v2_struct_0(D_284)
      | ~ m1_pre_topc(D_223,A_288)
      | v2_struct_0(D_223)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288)
      | ~ m1_pre_topc(D_223,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_377])).

tff(c_631,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_378])).

tff(c_705,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_50,c_62,c_60,c_50,c_42,c_30,c_26,c_38,c_631])).

tff(c_707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_44,c_218,c_705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.95  
% 4.60/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.95  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.60/1.95  
% 4.60/1.95  %Foreground sorts:
% 4.60/1.95  
% 4.60/1.95  
% 4.60/1.95  %Background operators:
% 4.60/1.95  
% 4.60/1.95  
% 4.60/1.95  %Foreground operators:
% 4.60/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.60/1.95  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.60/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.60/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.60/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.95  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.60/1.95  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.60/1.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.60/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.60/1.95  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.60/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.95  
% 4.60/1.98  tff(f_224, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(C, D) & m1_pre_topc(E, C)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((v1_funct_1(k3_tmap_1(A, B, D, C, F)) & v1_funct_2(k3_tmap_1(A, B, D, C, F), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, D, C, F), C, B)) & m1_subset_1(k3_tmap_1(A, B, D, C, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (((v1_funct_1(k3_tmap_1(A, B, D, E, F)) & v1_funct_2(k3_tmap_1(A, B, D, E, F), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, D, E, F), E, B)) & m1_subset_1(k3_tmap_1(A, B, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_tmap_1)).
% 4.60/1.98  tff(f_71, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 4.60/1.98  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 4.60/1.98  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 4.60/1.98  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, C, D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_tmap_1)).
% 4.60/1.98  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_34, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_190, plain, (![D_205, E_209, B_206, C_207, A_208]: (v1_funct_2(k3_tmap_1(A_208, B_206, C_207, D_205, E_209), u1_struct_0(D_205), u1_struct_0(B_206)) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_207), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0(C_207), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | ~m1_pre_topc(D_205, A_208) | ~m1_pre_topc(C_207, A_208) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_196, plain, (![A_208, D_205]: (v1_funct_2(k3_tmap_1(A_208, '#skF_2', '#skF_4', D_205, '#skF_6'), u1_struct_0(D_205), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_205, A_208) | ~m1_pre_topc('#skF_4', A_208) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(resolution, [status(thm)], [c_32, c_190])).
% 4.60/1.98  tff(c_207, plain, (![A_208, D_205]: (v1_funct_2(k3_tmap_1(A_208, '#skF_2', '#skF_4', D_205, '#skF_6'), u1_struct_0(D_205), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_205, A_208) | ~m1_pre_topc('#skF_4', A_208) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36, c_34, c_196])).
% 4.60/1.98  tff(c_209, plain, (![A_210, D_211]: (v1_funct_2(k3_tmap_1(A_210, '#skF_2', '#skF_4', D_211, '#skF_6'), u1_struct_0(D_211), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_211, A_210) | ~m1_pre_topc('#skF_4', A_210) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210) | v2_struct_0(A_210))), inference(negUnitSimplification, [status(thm)], [c_58, c_207])).
% 4.60/1.98  tff(c_145, plain, (![E_197, B_194, C_195, D_193, A_196]: (m1_subset_1(k3_tmap_1(A_196, B_194, C_195, D_193, E_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_193), u1_struct_0(B_194)))) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_195), u1_struct_0(B_194)))) | ~v1_funct_2(E_197, u1_struct_0(C_195), u1_struct_0(B_194)) | ~v1_funct_1(E_197) | ~m1_pre_topc(D_193, A_196) | ~m1_pre_topc(C_195, A_196) | ~l1_pre_topc(B_194) | ~v2_pre_topc(B_194) | v2_struct_0(B_194) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_90, plain, (![C_170, D_168, A_171, B_169, E_172]: (v1_funct_1(k3_tmap_1(A_171, B_169, C_170, D_168, E_172)) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170), u1_struct_0(B_169)))) | ~v1_funct_2(E_172, u1_struct_0(C_170), u1_struct_0(B_169)) | ~v1_funct_1(E_172) | ~m1_pre_topc(D_168, A_171) | ~m1_pre_topc(C_170, A_171) | ~l1_pre_topc(B_169) | ~v2_pre_topc(B_169) | v2_struct_0(B_169) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_94, plain, (![A_171, D_168]: (v1_funct_1(k3_tmap_1(A_171, '#skF_2', '#skF_4', D_168, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_168, A_171) | ~m1_pre_topc('#skF_4', A_171) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_32, c_90])).
% 4.60/1.98  tff(c_101, plain, (![A_171, D_168]: (v1_funct_1(k3_tmap_1(A_171, '#skF_2', '#skF_4', D_168, '#skF_6')) | ~m1_pre_topc(D_168, A_171) | ~m1_pre_topc('#skF_4', A_171) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36, c_34, c_94])).
% 4.60/1.98  tff(c_103, plain, (![A_173, D_174]: (v1_funct_1(k3_tmap_1(A_173, '#skF_2', '#skF_4', D_174, '#skF_6')) | ~m1_pre_topc(D_174, A_173) | ~m1_pre_topc('#skF_4', A_173) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(negUnitSimplification, [status(thm)], [c_58, c_101])).
% 4.60/1.98  tff(c_22, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_89, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_22])).
% 4.60/1.98  tff(c_106, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_103, c_89])).
% 4.60/1.98  tff(c_109, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_42, c_106])).
% 4.60/1.98  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_109])).
% 4.60/1.98  tff(c_112, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_22])).
% 4.60/1.98  tff(c_114, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_112])).
% 4.60/1.98  tff(c_152, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_145, c_114])).
% 4.60/1.98  tff(c_159, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_46, c_42, c_36, c_34, c_32, c_152])).
% 4.60/1.98  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_159])).
% 4.60/1.98  tff(c_162, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_112])).
% 4.60/1.98  tff(c_169, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_162])).
% 4.60/1.98  tff(c_212, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_209, c_169])).
% 4.60/1.98  tff(c_215, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_42, c_212])).
% 4.60/1.98  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_215])).
% 4.60/1.98  tff(c_218, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_162])).
% 4.60/1.98  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_30, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_26, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_38, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_28, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_269, plain, (![D_228, C_230, E_232, A_231, B_229]: (m1_subset_1(k3_tmap_1(A_231, B_229, C_230, D_228, E_232), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_228), u1_struct_0(B_229)))) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230), u1_struct_0(B_229)))) | ~v1_funct_2(E_232, u1_struct_0(C_230), u1_struct_0(B_229)) | ~v1_funct_1(E_232) | ~m1_pre_topc(D_228, A_231) | ~m1_pre_topc(C_230, A_231) | ~l1_pre_topc(B_229) | ~v2_pre_topc(B_229) | v2_struct_0(B_229) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_8, plain, (![B_6, C_7, E_9, D_8, A_5]: (v1_funct_2(k3_tmap_1(A_5, B_6, C_7, D_8, E_9), u1_struct_0(D_8), u1_struct_0(B_6)) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0(B_6)))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0(B_6)) | ~v1_funct_1(E_9) | ~m1_pre_topc(D_8, A_5) | ~m1_pre_topc(C_7, A_5) | ~l1_pre_topc(B_6) | ~v2_pre_topc(B_6) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_276, plain, (![D_228, D_8, C_230, A_5, E_232, A_231, B_229]: (v1_funct_2(k3_tmap_1(A_5, B_229, D_228, D_8, k3_tmap_1(A_231, B_229, C_230, D_228, E_232)), u1_struct_0(D_8), u1_struct_0(B_229)) | ~v1_funct_2(k3_tmap_1(A_231, B_229, C_230, D_228, E_232), u1_struct_0(D_228), u1_struct_0(B_229)) | ~v1_funct_1(k3_tmap_1(A_231, B_229, C_230, D_228, E_232)) | ~m1_pre_topc(D_8, A_5) | ~m1_pre_topc(D_228, A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_230), u1_struct_0(B_229)))) | ~v1_funct_2(E_232, u1_struct_0(C_230), u1_struct_0(B_229)) | ~v1_funct_1(E_232) | ~m1_pre_topc(D_228, A_231) | ~m1_pre_topc(C_230, A_231) | ~l1_pre_topc(B_229) | ~v2_pre_topc(B_229) | v2_struct_0(B_229) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_269, c_8])).
% 4.60/1.98  tff(c_250, plain, (![E_227, C_225, D_223, B_224, A_226]: (v1_funct_2(k3_tmap_1(A_226, B_224, C_225, D_223, E_227), u1_struct_0(D_223), u1_struct_0(B_224)) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_225), u1_struct_0(B_224)))) | ~v1_funct_2(E_227, u1_struct_0(C_225), u1_struct_0(B_224)) | ~v1_funct_1(E_227) | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc(C_225, A_226) | ~l1_pre_topc(B_224) | ~v2_pre_topc(B_224) | v2_struct_0(B_224) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_256, plain, (![A_226, D_223]: (v1_funct_2(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'), u1_struct_0(D_223), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_32, c_250])).
% 4.60/1.98  tff(c_267, plain, (![A_226, D_223]: (v1_funct_2(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'), u1_struct_0(D_223), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36, c_34, c_256])).
% 4.60/1.98  tff(c_268, plain, (![A_226, D_223]: (v1_funct_2(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'), u1_struct_0(D_223), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(negUnitSimplification, [status(thm)], [c_58, c_267])).
% 4.60/1.98  tff(c_10, plain, (![B_6, C_7, E_9, D_8, A_5]: (v1_funct_1(k3_tmap_1(A_5, B_6, C_7, D_8, E_9)) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0(B_6)))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0(B_6)) | ~v1_funct_1(E_9) | ~m1_pre_topc(D_8, A_5) | ~m1_pre_topc(C_7, A_5) | ~l1_pre_topc(B_6) | ~v2_pre_topc(B_6) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_315, plain, (![D_257, A_260, E_263, B_262, D_261, C_258, A_259]: (v1_funct_1(k3_tmap_1(A_260, B_262, D_261, D_257, k3_tmap_1(A_259, B_262, C_258, D_261, E_263))) | ~v1_funct_2(k3_tmap_1(A_259, B_262, C_258, D_261, E_263), u1_struct_0(D_261), u1_struct_0(B_262)) | ~v1_funct_1(k3_tmap_1(A_259, B_262, C_258, D_261, E_263)) | ~m1_pre_topc(D_257, A_260) | ~m1_pre_topc(D_261, A_260) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260) | ~m1_subset_1(E_263, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_258), u1_struct_0(B_262)))) | ~v1_funct_2(E_263, u1_struct_0(C_258), u1_struct_0(B_262)) | ~v1_funct_1(E_263) | ~m1_pre_topc(D_261, A_259) | ~m1_pre_topc(C_258, A_259) | ~l1_pre_topc(B_262) | ~v2_pre_topc(B_262) | v2_struct_0(B_262) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(resolution, [status(thm)], [c_269, c_10])).
% 4.60/1.98  tff(c_321, plain, (![A_260, D_223, D_257, A_226]: (v1_funct_1(k3_tmap_1(A_260, '#skF_2', D_223, D_257, k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'))) | ~v1_funct_1(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')) | ~m1_pre_topc(D_257, A_260) | ~m1_pre_topc(D_223, A_260) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_268, c_315])).
% 4.60/1.98  tff(c_336, plain, (![A_260, D_223, D_257, A_226]: (v1_funct_1(k3_tmap_1(A_260, '#skF_2', D_223, D_257, k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'))) | ~v1_funct_1(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')) | ~m1_pre_topc(D_257, A_260) | ~m1_pre_topc(D_223, A_260) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36, c_34, c_32, c_321])).
% 4.60/1.98  tff(c_337, plain, (![A_260, D_223, D_257, A_226]: (v1_funct_1(k3_tmap_1(A_260, '#skF_2', D_223, D_257, k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'))) | ~v1_funct_1(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')) | ~m1_pre_topc(D_257, A_260) | ~m1_pre_topc(D_223, A_260) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260) | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(negUnitSimplification, [status(thm)], [c_58, c_336])).
% 4.60/1.98  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_24, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.60/1.98  tff(c_113, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_22])).
% 4.60/1.98  tff(c_219, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_162])).
% 4.60/1.98  tff(c_163, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_112])).
% 4.60/1.98  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5]: (m1_subset_1(k3_tmap_1(A_5, B_6, C_7, D_8, E_9), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8), u1_struct_0(B_6)))) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0(B_6)))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0(B_6)) | ~v1_funct_1(E_9) | ~m1_pre_topc(D_8, A_5) | ~m1_pre_topc(C_7, A_5) | ~l1_pre_topc(B_6) | ~v2_pre_topc(B_6) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.98  tff(c_311, plain, (![E_255, D_256, B_254, A_253, F_252, C_251]: (r2_funct_2(u1_struct_0(E_255), u1_struct_0(B_254), k3_tmap_1(A_253, B_254, D_256, E_255, k3_tmap_1(A_253, B_254, C_251, D_256, F_252)), k3_tmap_1(A_253, B_254, C_251, E_255, F_252)) | ~m1_subset_1(F_252, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251), u1_struct_0(B_254)))) | ~v1_funct_2(F_252, u1_struct_0(C_251), u1_struct_0(B_254)) | ~v1_funct_1(F_252) | ~m1_pre_topc(E_255, D_256) | ~m1_pre_topc(D_256, C_251) | ~m1_pre_topc(E_255, A_253) | v2_struct_0(E_255) | ~m1_pre_topc(D_256, A_253) | v2_struct_0(D_256) | ~m1_pre_topc(C_251, A_253) | v2_struct_0(C_251) | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.60/1.98  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.98  tff(c_406, plain, (![D_313, A_314, B_312, C_311, F_315, E_316]: (k3_tmap_1(A_314, B_312, D_313, E_316, k3_tmap_1(A_314, B_312, C_311, D_313, F_315))=k3_tmap_1(A_314, B_312, C_311, E_316, F_315) | ~m1_subset_1(k3_tmap_1(A_314, B_312, C_311, E_316, F_315), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_316), u1_struct_0(B_312)))) | ~v1_funct_2(k3_tmap_1(A_314, B_312, C_311, E_316, F_315), u1_struct_0(E_316), u1_struct_0(B_312)) | ~v1_funct_1(k3_tmap_1(A_314, B_312, C_311, E_316, F_315)) | ~m1_subset_1(k3_tmap_1(A_314, B_312, D_313, E_316, k3_tmap_1(A_314, B_312, C_311, D_313, F_315)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_316), u1_struct_0(B_312)))) | ~v1_funct_2(k3_tmap_1(A_314, B_312, D_313, E_316, k3_tmap_1(A_314, B_312, C_311, D_313, F_315)), u1_struct_0(E_316), u1_struct_0(B_312)) | ~v1_funct_1(k3_tmap_1(A_314, B_312, D_313, E_316, k3_tmap_1(A_314, B_312, C_311, D_313, F_315))) | ~m1_subset_1(F_315, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_311), u1_struct_0(B_312)))) | ~v1_funct_2(F_315, u1_struct_0(C_311), u1_struct_0(B_312)) | ~v1_funct_1(F_315) | ~m1_pre_topc(E_316, D_313) | ~m1_pre_topc(D_313, C_311) | ~m1_pre_topc(E_316, A_314) | v2_struct_0(E_316) | ~m1_pre_topc(D_313, A_314) | v2_struct_0(D_313) | ~m1_pre_topc(C_311, A_314) | v2_struct_0(C_311) | ~l1_pre_topc(B_312) | ~v2_pre_topc(B_312) | v2_struct_0(B_312) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314))), inference(resolution, [status(thm)], [c_311, c_4])).
% 4.60/1.98  tff(c_490, plain, (![C_382, B_383, A_385, F_381, C_384, D_380]: (k3_tmap_1(A_385, B_383, C_384, D_380, k3_tmap_1(A_385, B_383, C_382, C_384, F_381))=k3_tmap_1(A_385, B_383, C_382, D_380, F_381) | ~m1_subset_1(k3_tmap_1(A_385, B_383, C_382, D_380, F_381), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_380), u1_struct_0(B_383)))) | ~v1_funct_2(k3_tmap_1(A_385, B_383, C_382, D_380, F_381), u1_struct_0(D_380), u1_struct_0(B_383)) | ~v1_funct_1(k3_tmap_1(A_385, B_383, C_382, D_380, F_381)) | ~v1_funct_2(k3_tmap_1(A_385, B_383, C_384, D_380, k3_tmap_1(A_385, B_383, C_382, C_384, F_381)), u1_struct_0(D_380), u1_struct_0(B_383)) | ~v1_funct_1(k3_tmap_1(A_385, B_383, C_384, D_380, k3_tmap_1(A_385, B_383, C_382, C_384, F_381))) | ~m1_subset_1(F_381, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_382), u1_struct_0(B_383)))) | ~v1_funct_2(F_381, u1_struct_0(C_382), u1_struct_0(B_383)) | ~v1_funct_1(F_381) | ~m1_pre_topc(D_380, C_384) | ~m1_pre_topc(C_384, C_382) | v2_struct_0(D_380) | v2_struct_0(C_384) | ~m1_pre_topc(C_382, A_385) | v2_struct_0(C_382) | ~m1_subset_1(k3_tmap_1(A_385, B_383, C_382, C_384, F_381), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384), u1_struct_0(B_383)))) | ~v1_funct_2(k3_tmap_1(A_385, B_383, C_382, C_384, F_381), u1_struct_0(C_384), u1_struct_0(B_383)) | ~v1_funct_1(k3_tmap_1(A_385, B_383, C_382, C_384, F_381)) | ~m1_pre_topc(D_380, A_385) | ~m1_pre_topc(C_384, A_385) | ~l1_pre_topc(B_383) | ~v2_pre_topc(B_383) | v2_struct_0(B_383) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(resolution, [status(thm)], [c_6, c_406])).
% 4.60/1.98  tff(c_494, plain, (![C_384]: (k3_tmap_1('#skF_1', '#skF_2', C_384, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', C_384, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', C_384, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', C_384) | ~m1_pre_topc(C_384, '#skF_4') | v2_struct_0('#skF_5') | v2_struct_0(C_384) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'), u1_struct_0(C_384), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc(C_384, '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_163, c_490])).
% 4.60/1.98  tff(c_500, plain, (![C_384]: (k3_tmap_1('#skF_1', '#skF_2', C_384, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', C_384, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', C_384, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'))) | ~m1_pre_topc('#skF_5', C_384) | ~m1_pre_topc(C_384, '#skF_4') | v2_struct_0('#skF_5') | v2_struct_0(C_384) | v2_struct_0('#skF_4') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6'), u1_struct_0(C_384), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_384, '#skF_6')) | ~m1_pre_topc(C_384, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_42, c_46, c_36, c_34, c_32, c_113, c_219, c_494])).
% 4.60/1.98  tff(c_506, plain, (![C_386]: (k3_tmap_1('#skF_1', '#skF_2', C_386, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_386, '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', C_386, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_386, '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', C_386, '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_386, '#skF_6'))) | ~m1_pre_topc('#skF_5', C_386) | ~m1_pre_topc(C_386, '#skF_4') | v2_struct_0(C_386) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_386, '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_386), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_386, '#skF_6'), u1_struct_0(C_386), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', C_386, '#skF_6')) | ~m1_pre_topc(C_386, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_48, c_44, c_500])).
% 4.60/1.98  tff(c_516, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_506])).
% 4.60/1.98  tff(c_527, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30, c_28, c_40, c_38, c_516])).
% 4.60/1.98  tff(c_528, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_52, c_527])).
% 4.60/1.98  tff(c_529, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')))), inference(splitLeft, [status(thm)], [c_528])).
% 4.60/1.98  tff(c_532, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_337, c_529])).
% 4.60/1.98  tff(c_538, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_50, c_42, c_30, c_532])).
% 4.60/1.98  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_538])).
% 4.60/1.98  tff(c_541, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_528])).
% 4.60/1.98  tff(c_544, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_541])).
% 4.60/1.98  tff(c_547, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_276, c_544])).
% 4.60/1.98  tff(c_553, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_46, c_50, c_36, c_34, c_32, c_42, c_30, c_28, c_547])).
% 4.60/1.98  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_553])).
% 4.60/1.98  tff(c_556, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_541])).
% 4.60/1.98  tff(c_282, plain, (![E_239, A_243, B_242, D_241, C_240]: (v5_pre_topc(k3_tmap_1(A_243, B_242, C_240, D_241, E_239), D_241, B_242) | ~m1_pre_topc(D_241, C_240) | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240), u1_struct_0(B_242)))) | ~v5_pre_topc(E_239, C_240, B_242) | ~v1_funct_2(E_239, u1_struct_0(C_240), u1_struct_0(B_242)) | ~v1_funct_1(E_239) | ~m1_pre_topc(D_241, A_243) | v2_struct_0(D_241) | ~m1_pre_topc(C_240, A_243) | v2_struct_0(C_240) | ~l1_pre_topc(B_242) | ~v2_pre_topc(B_242) | v2_struct_0(B_242) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.60/1.98  tff(c_353, plain, (![B_285, D_284, A_288, E_289, D_283, A_287, C_286]: (v5_pre_topc(k3_tmap_1(A_288, B_285, D_283, D_284, k3_tmap_1(A_287, B_285, C_286, D_283, E_289)), D_284, B_285) | ~m1_pre_topc(D_284, D_283) | ~v5_pre_topc(k3_tmap_1(A_287, B_285, C_286, D_283, E_289), D_283, B_285) | ~v1_funct_2(k3_tmap_1(A_287, B_285, C_286, D_283, E_289), u1_struct_0(D_283), u1_struct_0(B_285)) | ~v1_funct_1(k3_tmap_1(A_287, B_285, C_286, D_283, E_289)) | ~m1_pre_topc(D_284, A_288) | v2_struct_0(D_284) | ~m1_pre_topc(D_283, A_288) | v2_struct_0(D_283) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_286), u1_struct_0(B_285)))) | ~v1_funct_2(E_289, u1_struct_0(C_286), u1_struct_0(B_285)) | ~v1_funct_1(E_289) | ~m1_pre_topc(D_283, A_287) | ~m1_pre_topc(C_286, A_287) | ~l1_pre_topc(B_285) | ~v2_pre_topc(B_285) | v2_struct_0(B_285) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(resolution, [status(thm)], [c_6, c_282])).
% 4.60/1.98  tff(c_361, plain, (![A_288, D_223, D_284, A_226]: (v5_pre_topc(k3_tmap_1(A_288, '#skF_2', D_223, D_284, k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')), D_284, '#skF_2') | ~m1_pre_topc(D_284, D_223) | ~v5_pre_topc(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'), D_223, '#skF_2') | ~v1_funct_1(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')) | ~m1_pre_topc(D_284, A_288) | v2_struct_0(D_284) | ~m1_pre_topc(D_223, A_288) | v2_struct_0(D_223) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_268, c_353])).
% 4.60/1.98  tff(c_377, plain, (![A_288, D_223, D_284, A_226]: (v5_pre_topc(k3_tmap_1(A_288, '#skF_2', D_223, D_284, k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')), D_284, '#skF_2') | ~m1_pre_topc(D_284, D_223) | ~v5_pre_topc(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'), D_223, '#skF_2') | ~v1_funct_1(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')) | ~m1_pre_topc(D_284, A_288) | v2_struct_0(D_284) | ~m1_pre_topc(D_223, A_288) | v2_struct_0(D_223) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36, c_34, c_32, c_361])).
% 4.60/1.98  tff(c_378, plain, (![A_288, D_223, D_284, A_226]: (v5_pre_topc(k3_tmap_1(A_288, '#skF_2', D_223, D_284, k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')), D_284, '#skF_2') | ~m1_pre_topc(D_284, D_223) | ~v5_pre_topc(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6'), D_223, '#skF_2') | ~v1_funct_1(k3_tmap_1(A_226, '#skF_2', '#skF_4', D_223, '#skF_6')) | ~m1_pre_topc(D_284, A_288) | v2_struct_0(D_284) | ~m1_pre_topc(D_223, A_288) | v2_struct_0(D_223) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288) | ~m1_pre_topc(D_223, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(negUnitSimplification, [status(thm)], [c_58, c_377])).
% 4.60/1.98  tff(c_631, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~m1_pre_topc('#skF_5', '#skF_3') | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2') | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_556, c_378])).
% 4.60/1.98  tff(c_705, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_50, c_62, c_60, c_50, c_42, c_30, c_26, c_38, c_631])).
% 4.60/1.98  tff(c_707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_44, c_218, c_705])).
% 4.60/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.98  
% 4.60/1.98  Inference rules
% 4.60/1.98  ----------------------
% 4.60/1.98  #Ref     : 0
% 4.60/1.98  #Sup     : 111
% 4.60/1.98  #Fact    : 0
% 4.60/1.98  #Define  : 0
% 4.60/1.98  #Split   : 7
% 4.60/1.98  #Chain   : 0
% 4.60/1.98  #Close   : 0
% 4.60/1.98  
% 4.60/1.98  Ordering : KBO
% 4.60/1.98  
% 4.60/1.98  Simplification rules
% 4.60/1.98  ----------------------
% 4.60/1.98  #Subsume      : 26
% 4.60/1.98  #Demod        : 504
% 4.60/1.98  #Tautology    : 8
% 4.60/1.98  #SimpNegUnit  : 69
% 4.60/1.98  #BackRed      : 2
% 4.60/1.98  
% 4.60/1.98  #Partial instantiations: 0
% 4.60/1.98  #Strategies tried      : 1
% 4.60/1.98  
% 4.60/1.98  Timing (in seconds)
% 4.60/1.98  ----------------------
% 4.60/1.98  Preprocessing        : 0.55
% 4.60/1.98  Parsing              : 0.31
% 4.60/1.98  CNF conversion       : 0.07
% 4.60/1.98  Main loop            : 0.58
% 4.60/1.98  Inferencing          : 0.21
% 4.60/1.98  Reduction            : 0.19
% 4.60/1.98  Demodulation         : 0.14
% 4.60/1.98  BG Simplification    : 0.02
% 4.60/1.98  Subsumption          : 0.13
% 4.60/1.98  Abstraction          : 0.02
% 4.60/1.98  MUC search           : 0.00
% 4.60/1.98  Cooper               : 0.00
% 4.60/1.98  Total                : 1.17
% 4.60/1.98  Index Insertion      : 0.00
% 4.60/1.98  Index Deletion       : 0.00
% 4.60/1.98  Index Matching       : 0.00
% 4.60/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
