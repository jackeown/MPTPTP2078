%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:10 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 409 expanded)
%              Number of leaves         :   33 ( 178 expanded)
%              Depth                    :   13
%              Number of atoms          :  389 (3558 expanded)
%              Number of equality atoms :   22 ( 183 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
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
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => ( ! [G] :
                                    ( m1_subset_1(G,u1_struct_0(D))
                                   => ( r2_hidden(G,u1_struct_0(C))
                                     => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,G) = k1_funct_1(F,G) ) )
                               => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tmap_1)).

tff(f_100,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_144,axiom,(
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
                & m1_pre_topc(C,B) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( r2_hidden(F,u1_struct_0(C))
                             => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_34,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_30,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_133,plain,(
    ! [B_249,D_247,A_248,E_250,C_251] :
      ( k3_tmap_1(A_248,B_249,C_251,D_247,E_250) = k2_partfun1(u1_struct_0(C_251),u1_struct_0(B_249),E_250,u1_struct_0(D_247))
      | ~ m1_pre_topc(D_247,C_251)
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251),u1_struct_0(B_249))))
      | ~ v1_funct_2(E_250,u1_struct_0(C_251),u1_struct_0(B_249))
      | ~ v1_funct_1(E_250)
      | ~ m1_pre_topc(D_247,A_248)
      | ~ m1_pre_topc(C_251,A_248)
      | ~ l1_pre_topc(B_249)
      | ~ v2_pre_topc(B_249)
      | v2_struct_0(B_249)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_137,plain,(
    ! [A_248,D_247] :
      ( k3_tmap_1(A_248,'#skF_3','#skF_5',D_247,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_247))
      | ~ m1_pre_topc(D_247,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_247,A_248)
      | ~ m1_pre_topc('#skF_5',A_248)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_144,plain,(
    ! [A_248,D_247] :
      ( k3_tmap_1(A_248,'#skF_3','#skF_5',D_247,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_247))
      | ~ m1_pre_topc(D_247,'#skF_5')
      | ~ m1_pre_topc(D_247,A_248)
      | ~ m1_pre_topc('#skF_5',A_248)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_137])).

tff(c_180,plain,(
    ! [A_259,D_260] :
      ( k3_tmap_1(A_259,'#skF_3','#skF_5',D_260,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_260))
      | ~ m1_pre_topc(D_260,'#skF_5')
      | ~ m1_pre_topc(D_260,A_259)
      | ~ m1_pre_topc('#skF_5',A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_144])).

tff(c_182,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_180])).

tff(c_189,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_26,c_182])).

tff(c_190,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_189])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_72,plain,(
    ! [B_238,A_239] :
      ( v2_pre_topc(B_238)
      | ~ m1_pre_topc(B_238,A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_72])).

tff(c_90,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_81])).

tff(c_53,plain,(
    ! [B_236,A_237] :
      ( l1_pre_topc(B_236)
      | ~ m1_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_69,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_102,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k2_partfun1(u1_struct_0(A_241),u1_struct_0(B_242),C_243,u1_struct_0(D_244)) = k2_tmap_1(A_241,B_242,C_243,D_244)
      | ~ m1_pre_topc(D_244,A_241)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241),u1_struct_0(B_242))))
      | ~ v1_funct_2(C_243,u1_struct_0(A_241),u1_struct_0(B_242))
      | ~ v1_funct_1(C_243)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_244)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_244)
      | ~ m1_pre_topc(D_244,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_113,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_244)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_244)
      | ~ m1_pre_topc(D_244,'#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_69,c_44,c_42,c_32,c_30,c_106])).

tff(c_114,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_244)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_244)
      | ~ m1_pre_topc(D_244,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_46,c_113])).

tff(c_202,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_114])).

tff(c_209,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_202])).

tff(c_16,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_214,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_16])).

tff(c_24,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_22,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_20,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_237,plain,(
    ! [D_265,C_264,A_262,E_261,B_263] :
      ( m1_subset_1('#skF_1'(E_261,A_262,B_263,C_264,D_265),u1_struct_0(B_263))
      | r2_funct_2(u1_struct_0(C_264),u1_struct_0(A_262),k2_tmap_1(B_263,A_262,D_265,C_264),E_261)
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_264),u1_struct_0(A_262))))
      | ~ v1_funct_2(E_261,u1_struct_0(C_264),u1_struct_0(A_262))
      | ~ v1_funct_1(E_261)
      | ~ m1_subset_1(D_265,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263),u1_struct_0(A_262))))
      | ~ v1_funct_2(D_265,u1_struct_0(B_263),u1_struct_0(A_262))
      | ~ v1_funct_1(D_265)
      | ~ m1_pre_topc(C_264,B_263)
      | v2_struct_0(C_264)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_239,plain,(
    ! [B_263,D_265] :
      ( m1_subset_1('#skF_1'('#skF_7','#skF_3',B_263,'#skF_4',D_265),u1_struct_0(B_263))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1(B_263,'#skF_3',D_265,'#skF_4'),'#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_265,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_265,u1_struct_0(B_263),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_265)
      | ~ m1_pre_topc('#skF_4',B_263)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_237])).

tff(c_244,plain,(
    ! [B_263,D_265] :
      ( m1_subset_1('#skF_1'('#skF_7','#skF_3',B_263,'#skF_4',D_265),u1_struct_0(B_263))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1(B_263,'#skF_3',D_265,'#skF_4'),'#skF_7')
      | ~ m1_subset_1(D_265,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_265,u1_struct_0(B_263),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_265)
      | ~ m1_pre_topc('#skF_4',B_263)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_24,c_22,c_239])).

tff(c_251,plain,(
    ! [B_266,D_267] :
      ( m1_subset_1('#skF_1'('#skF_7','#skF_3',B_266,'#skF_4',D_267),u1_struct_0(B_266))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1(B_266,'#skF_3',D_267,'#skF_4'),'#skF_7')
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_266),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_267,u1_struct_0(B_266),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_267)
      | ~ m1_pre_topc('#skF_4',B_266)
      | ~ l1_pre_topc(B_266)
      | ~ v2_pre_topc(B_266)
      | v2_struct_0(B_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_244])).

tff(c_255,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_251])).

tff(c_262,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_69,c_26,c_32,c_30,c_255])).

tff(c_263,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_214,c_262])).

tff(c_166,plain,(
    ! [B_256,A_255,C_257,E_254,D_258] :
      ( r2_hidden('#skF_1'(E_254,A_255,B_256,C_257,D_258),u1_struct_0(C_257))
      | r2_funct_2(u1_struct_0(C_257),u1_struct_0(A_255),k2_tmap_1(B_256,A_255,D_258,C_257),E_254)
      | ~ m1_subset_1(E_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257),u1_struct_0(A_255))))
      | ~ v1_funct_2(E_254,u1_struct_0(C_257),u1_struct_0(A_255))
      | ~ v1_funct_1(E_254)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256),u1_struct_0(A_255))))
      | ~ v1_funct_2(D_258,u1_struct_0(B_256),u1_struct_0(A_255))
      | ~ v1_funct_1(D_258)
      | ~ m1_pre_topc(C_257,B_256)
      | v2_struct_0(C_257)
      | ~ l1_pre_topc(B_256)
      | ~ v2_pre_topc(B_256)
      | v2_struct_0(B_256)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_168,plain,(
    ! [B_256,D_258] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_3',B_256,'#skF_4',D_258),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1(B_256,'#skF_3',D_258,'#skF_4'),'#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_258,u1_struct_0(B_256),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_258)
      | ~ m1_pre_topc('#skF_4',B_256)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_256)
      | ~ v2_pre_topc(B_256)
      | v2_struct_0(B_256)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_166])).

tff(c_173,plain,(
    ! [B_256,D_258] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_3',B_256,'#skF_4',D_258),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1(B_256,'#skF_3',D_258,'#skF_4'),'#skF_7')
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_258,u1_struct_0(B_256),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_258)
      | ~ m1_pre_topc('#skF_4',B_256)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_256)
      | ~ v2_pre_topc(B_256)
      | v2_struct_0(B_256)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_24,c_22,c_168])).

tff(c_292,plain,(
    ! [B_272,D_273] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_3',B_272,'#skF_4',D_273),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1(B_272,'#skF_3',D_273,'#skF_4'),'#skF_7')
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_272),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_273,u1_struct_0(B_272),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_273)
      | ~ m1_pre_topc('#skF_4',B_272)
      | ~ l1_pre_topc(B_272)
      | ~ v2_pre_topc(B_272)
      | v2_struct_0(B_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_173])).

tff(c_298,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_292])).

tff(c_305,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_69,c_26,c_32,c_30,c_298])).

tff(c_306,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_214,c_305])).

tff(c_18,plain,(
    ! [G_235] :
      ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',G_235) = k1_funct_1('#skF_7',G_235)
      | ~ r2_hidden(G_235,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_235,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_307,plain,(
    ! [E_274,D_278,C_277,B_276,A_275] :
      ( k3_funct_2(u1_struct_0(B_276),u1_struct_0(A_275),D_278,'#skF_1'(E_274,A_275,B_276,C_277,D_278)) != k1_funct_1(E_274,'#skF_1'(E_274,A_275,B_276,C_277,D_278))
      | r2_funct_2(u1_struct_0(C_277),u1_struct_0(A_275),k2_tmap_1(B_276,A_275,D_278,C_277),E_274)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277),u1_struct_0(A_275))))
      | ~ v1_funct_2(E_274,u1_struct_0(C_277),u1_struct_0(A_275))
      | ~ v1_funct_1(E_274)
      | ~ m1_subset_1(D_278,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_276),u1_struct_0(A_275))))
      | ~ v1_funct_2(D_278,u1_struct_0(B_276),u1_struct_0(A_275))
      | ~ v1_funct_1(D_278)
      | ~ m1_pre_topc(C_277,B_276)
      | v2_struct_0(C_277)
      | ~ l1_pre_topc(B_276)
      | ~ v2_pre_topc(B_276)
      | v2_struct_0(B_276)
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_310,plain,(
    ! [E_274,C_277] :
      ( k1_funct_1(E_274,'#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6')) != k1_funct_1('#skF_7','#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'))
      | r2_funct_2(u1_struct_0(C_277),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6',C_277),E_274)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_274,u1_struct_0(C_277),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_274)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(C_277,'#skF_5')
      | v2_struct_0(C_277)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_307])).

tff(c_312,plain,(
    ! [E_274,C_277] :
      ( k1_funct_1(E_274,'#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6')) != k1_funct_1('#skF_7','#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'))
      | r2_funct_2(u1_struct_0(C_277),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6',C_277),E_274)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_274,u1_struct_0(C_277),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_274)
      | ~ m1_pre_topc(C_277,'#skF_5')
      | v2_struct_0(C_277)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_90,c_69,c_32,c_30,c_28,c_310])).

tff(c_313,plain,(
    ! [E_274,C_277] :
      ( k1_funct_1(E_274,'#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6')) != k1_funct_1('#skF_7','#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'))
      | r2_funct_2(u1_struct_0(C_277),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6',C_277),E_274)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_274,u1_struct_0(C_277),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_274)
      | ~ m1_pre_topc(C_277,'#skF_5')
      | v2_struct_0(C_277)
      | ~ r2_hidden('#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(E_274,'#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36,c_312])).

tff(c_316,plain,(
    ! [C_277] :
      ( r2_funct_2(u1_struct_0(C_277),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6',C_277),'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0(C_277),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(C_277,'#skF_5')
      | v2_struct_0(C_277)
      | ~ r2_hidden('#skF_1'('#skF_7','#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_5',C_277,'#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_313])).

tff(c_320,plain,(
    ! [C_281] :
      ( r2_funct_2(u1_struct_0(C_281),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6',C_281),'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_281),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0(C_281),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(C_281,'#skF_5')
      | v2_struct_0(C_281)
      | ~ r2_hidden('#skF_1'('#skF_7','#skF_3','#skF_5',C_281,'#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_5',C_281,'#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_316])).

tff(c_322,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_5','#skF_4','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_320])).

tff(c_325,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_306,c_26,c_22,c_322])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_214,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.36  
% 2.72/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.37  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.72/1.37  
% 2.72/1.37  %Foreground sorts:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Background operators:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Foreground operators:
% 2.72/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.72/1.37  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.72/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.72/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.72/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.72/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.72/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.72/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.72/1.37  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.72/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.72/1.37  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.72/1.37  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.72/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.37  
% 2.72/1.39  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((![G]: (m1_subset_1(G, u1_struct_0(D)) => (r2_hidden(G, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, G) = k1_funct_1(F, G))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tmap_1)).
% 2.72/1.39  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.72/1.39  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.72/1.39  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.72/1.39  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.72/1.39  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 2.72/1.39  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_34, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_32, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_30, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_133, plain, (![B_249, D_247, A_248, E_250, C_251]: (k3_tmap_1(A_248, B_249, C_251, D_247, E_250)=k2_partfun1(u1_struct_0(C_251), u1_struct_0(B_249), E_250, u1_struct_0(D_247)) | ~m1_pre_topc(D_247, C_251) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251), u1_struct_0(B_249)))) | ~v1_funct_2(E_250, u1_struct_0(C_251), u1_struct_0(B_249)) | ~v1_funct_1(E_250) | ~m1_pre_topc(D_247, A_248) | ~m1_pre_topc(C_251, A_248) | ~l1_pre_topc(B_249) | ~v2_pre_topc(B_249) | v2_struct_0(B_249) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.72/1.39  tff(c_137, plain, (![A_248, D_247]: (k3_tmap_1(A_248, '#skF_3', '#skF_5', D_247, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_247)) | ~m1_pre_topc(D_247, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_247, A_248) | ~m1_pre_topc('#skF_5', A_248) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(resolution, [status(thm)], [c_28, c_133])).
% 2.72/1.39  tff(c_144, plain, (![A_248, D_247]: (k3_tmap_1(A_248, '#skF_3', '#skF_5', D_247, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_247)) | ~m1_pre_topc(D_247, '#skF_5') | ~m1_pre_topc(D_247, A_248) | ~m1_pre_topc('#skF_5', A_248) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_137])).
% 2.72/1.39  tff(c_180, plain, (![A_259, D_260]: (k3_tmap_1(A_259, '#skF_3', '#skF_5', D_260, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_260)) | ~m1_pre_topc(D_260, '#skF_5') | ~m1_pre_topc(D_260, A_259) | ~m1_pre_topc('#skF_5', A_259) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(negUnitSimplification, [status(thm)], [c_46, c_144])).
% 2.72/1.39  tff(c_182, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_180])).
% 2.72/1.39  tff(c_189, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_26, c_182])).
% 2.72/1.39  tff(c_190, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_189])).
% 2.72/1.39  tff(c_36, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_72, plain, (![B_238, A_239]: (v2_pre_topc(B_238) | ~m1_pre_topc(B_238, A_239) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.72/1.39  tff(c_81, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_72])).
% 2.72/1.39  tff(c_90, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_81])).
% 2.72/1.39  tff(c_53, plain, (![B_236, A_237]: (l1_pre_topc(B_236) | ~m1_pre_topc(B_236, A_237) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.39  tff(c_62, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_53])).
% 2.72/1.39  tff(c_69, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 2.72/1.39  tff(c_102, plain, (![A_241, B_242, C_243, D_244]: (k2_partfun1(u1_struct_0(A_241), u1_struct_0(B_242), C_243, u1_struct_0(D_244))=k2_tmap_1(A_241, B_242, C_243, D_244) | ~m1_pre_topc(D_244, A_241) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241), u1_struct_0(B_242)))) | ~v1_funct_2(C_243, u1_struct_0(A_241), u1_struct_0(B_242)) | ~v1_funct_1(C_243) | ~l1_pre_topc(B_242) | ~v2_pre_topc(B_242) | v2_struct_0(B_242) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.39  tff(c_106, plain, (![D_244]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_244))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_244) | ~m1_pre_topc(D_244, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_102])).
% 2.72/1.39  tff(c_113, plain, (![D_244]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_244))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_244) | ~m1_pre_topc(D_244, '#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_69, c_44, c_42, c_32, c_30, c_106])).
% 2.72/1.39  tff(c_114, plain, (![D_244]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_244))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_244) | ~m1_pre_topc(D_244, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_36, c_46, c_113])).
% 2.72/1.39  tff(c_202, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_190, c_114])).
% 2.72/1.39  tff(c_209, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_202])).
% 2.72/1.39  tff(c_16, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_214, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_16])).
% 2.72/1.39  tff(c_24, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_22, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_20, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_237, plain, (![D_265, C_264, A_262, E_261, B_263]: (m1_subset_1('#skF_1'(E_261, A_262, B_263, C_264, D_265), u1_struct_0(B_263)) | r2_funct_2(u1_struct_0(C_264), u1_struct_0(A_262), k2_tmap_1(B_263, A_262, D_265, C_264), E_261) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_264), u1_struct_0(A_262)))) | ~v1_funct_2(E_261, u1_struct_0(C_264), u1_struct_0(A_262)) | ~v1_funct_1(E_261) | ~m1_subset_1(D_265, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263), u1_struct_0(A_262)))) | ~v1_funct_2(D_265, u1_struct_0(B_263), u1_struct_0(A_262)) | ~v1_funct_1(D_265) | ~m1_pre_topc(C_264, B_263) | v2_struct_0(C_264) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.72/1.39  tff(c_239, plain, (![B_263, D_265]: (m1_subset_1('#skF_1'('#skF_7', '#skF_3', B_263, '#skF_4', D_265), u1_struct_0(B_263)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1(B_263, '#skF_3', D_265, '#skF_4'), '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_265, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263), u1_struct_0('#skF_3')))) | ~v1_funct_2(D_265, u1_struct_0(B_263), u1_struct_0('#skF_3')) | ~v1_funct_1(D_265) | ~m1_pre_topc('#skF_4', B_263) | v2_struct_0('#skF_4') | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_237])).
% 2.72/1.39  tff(c_244, plain, (![B_263, D_265]: (m1_subset_1('#skF_1'('#skF_7', '#skF_3', B_263, '#skF_4', D_265), u1_struct_0(B_263)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1(B_263, '#skF_3', D_265, '#skF_4'), '#skF_7') | ~m1_subset_1(D_265, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263), u1_struct_0('#skF_3')))) | ~v1_funct_2(D_265, u1_struct_0(B_263), u1_struct_0('#skF_3')) | ~v1_funct_1(D_265) | ~m1_pre_topc('#skF_4', B_263) | v2_struct_0('#skF_4') | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_24, c_22, c_239])).
% 2.72/1.39  tff(c_251, plain, (![B_266, D_267]: (m1_subset_1('#skF_1'('#skF_7', '#skF_3', B_266, '#skF_4', D_267), u1_struct_0(B_266)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1(B_266, '#skF_3', D_267, '#skF_4'), '#skF_7') | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_266), u1_struct_0('#skF_3')))) | ~v1_funct_2(D_267, u1_struct_0(B_266), u1_struct_0('#skF_3')) | ~v1_funct_1(D_267) | ~m1_pre_topc('#skF_4', B_266) | ~l1_pre_topc(B_266) | ~v2_pre_topc(B_266) | v2_struct_0(B_266))), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_244])).
% 2.72/1.39  tff(c_255, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_251])).
% 2.72/1.39  tff(c_262, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_69, c_26, c_32, c_30, c_255])).
% 2.72/1.39  tff(c_263, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_36, c_214, c_262])).
% 2.72/1.39  tff(c_166, plain, (![B_256, A_255, C_257, E_254, D_258]: (r2_hidden('#skF_1'(E_254, A_255, B_256, C_257, D_258), u1_struct_0(C_257)) | r2_funct_2(u1_struct_0(C_257), u1_struct_0(A_255), k2_tmap_1(B_256, A_255, D_258, C_257), E_254) | ~m1_subset_1(E_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257), u1_struct_0(A_255)))) | ~v1_funct_2(E_254, u1_struct_0(C_257), u1_struct_0(A_255)) | ~v1_funct_1(E_254) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256), u1_struct_0(A_255)))) | ~v1_funct_2(D_258, u1_struct_0(B_256), u1_struct_0(A_255)) | ~v1_funct_1(D_258) | ~m1_pre_topc(C_257, B_256) | v2_struct_0(C_257) | ~l1_pre_topc(B_256) | ~v2_pre_topc(B_256) | v2_struct_0(B_256) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.72/1.39  tff(c_168, plain, (![B_256, D_258]: (r2_hidden('#skF_1'('#skF_7', '#skF_3', B_256, '#skF_4', D_258), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1(B_256, '#skF_3', D_258, '#skF_4'), '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256), u1_struct_0('#skF_3')))) | ~v1_funct_2(D_258, u1_struct_0(B_256), u1_struct_0('#skF_3')) | ~v1_funct_1(D_258) | ~m1_pre_topc('#skF_4', B_256) | v2_struct_0('#skF_4') | ~l1_pre_topc(B_256) | ~v2_pre_topc(B_256) | v2_struct_0(B_256) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_166])).
% 2.72/1.39  tff(c_173, plain, (![B_256, D_258]: (r2_hidden('#skF_1'('#skF_7', '#skF_3', B_256, '#skF_4', D_258), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1(B_256, '#skF_3', D_258, '#skF_4'), '#skF_7') | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256), u1_struct_0('#skF_3')))) | ~v1_funct_2(D_258, u1_struct_0(B_256), u1_struct_0('#skF_3')) | ~v1_funct_1(D_258) | ~m1_pre_topc('#skF_4', B_256) | v2_struct_0('#skF_4') | ~l1_pre_topc(B_256) | ~v2_pre_topc(B_256) | v2_struct_0(B_256) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_24, c_22, c_168])).
% 2.72/1.39  tff(c_292, plain, (![B_272, D_273]: (r2_hidden('#skF_1'('#skF_7', '#skF_3', B_272, '#skF_4', D_273), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1(B_272, '#skF_3', D_273, '#skF_4'), '#skF_7') | ~m1_subset_1(D_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_272), u1_struct_0('#skF_3')))) | ~v1_funct_2(D_273, u1_struct_0(B_272), u1_struct_0('#skF_3')) | ~v1_funct_1(D_273) | ~m1_pre_topc('#skF_4', B_272) | ~l1_pre_topc(B_272) | ~v2_pre_topc(B_272) | v2_struct_0(B_272))), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_173])).
% 2.72/1.39  tff(c_298, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_292])).
% 2.72/1.39  tff(c_305, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_69, c_26, c_32, c_30, c_298])).
% 2.72/1.39  tff(c_306, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_214, c_305])).
% 2.72/1.39  tff(c_18, plain, (![G_235]: (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', G_235)=k1_funct_1('#skF_7', G_235) | ~r2_hidden(G_235, u1_struct_0('#skF_4')) | ~m1_subset_1(G_235, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.72/1.39  tff(c_307, plain, (![E_274, D_278, C_277, B_276, A_275]: (k3_funct_2(u1_struct_0(B_276), u1_struct_0(A_275), D_278, '#skF_1'(E_274, A_275, B_276, C_277, D_278))!=k1_funct_1(E_274, '#skF_1'(E_274, A_275, B_276, C_277, D_278)) | r2_funct_2(u1_struct_0(C_277), u1_struct_0(A_275), k2_tmap_1(B_276, A_275, D_278, C_277), E_274) | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277), u1_struct_0(A_275)))) | ~v1_funct_2(E_274, u1_struct_0(C_277), u1_struct_0(A_275)) | ~v1_funct_1(E_274) | ~m1_subset_1(D_278, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_276), u1_struct_0(A_275)))) | ~v1_funct_2(D_278, u1_struct_0(B_276), u1_struct_0(A_275)) | ~v1_funct_1(D_278) | ~m1_pre_topc(C_277, B_276) | v2_struct_0(C_277) | ~l1_pre_topc(B_276) | ~v2_pre_topc(B_276) | v2_struct_0(B_276) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.72/1.39  tff(c_310, plain, (![E_274, C_277]: (k1_funct_1(E_274, '#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'))!=k1_funct_1('#skF_7', '#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6')) | r2_funct_2(u1_struct_0(C_277), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', C_277), E_274) | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277), u1_struct_0('#skF_3')))) | ~v1_funct_2(E_274, u1_struct_0(C_277), u1_struct_0('#skF_3')) | ~v1_funct_1(E_274) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(C_277, '#skF_5') | v2_struct_0(C_277) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_307])).
% 2.72/1.39  tff(c_312, plain, (![E_274, C_277]: (k1_funct_1(E_274, '#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'))!=k1_funct_1('#skF_7', '#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6')) | r2_funct_2(u1_struct_0(C_277), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', C_277), E_274) | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277), u1_struct_0('#skF_3')))) | ~v1_funct_2(E_274, u1_struct_0(C_277), u1_struct_0('#skF_3')) | ~v1_funct_1(E_274) | ~m1_pre_topc(C_277, '#skF_5') | v2_struct_0(C_277) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_90, c_69, c_32, c_30, c_28, c_310])).
% 2.72/1.39  tff(c_313, plain, (![E_274, C_277]: (k1_funct_1(E_274, '#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'))!=k1_funct_1('#skF_7', '#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6')) | r2_funct_2(u1_struct_0(C_277), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', C_277), E_274) | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277), u1_struct_0('#skF_3')))) | ~v1_funct_2(E_274, u1_struct_0(C_277), u1_struct_0('#skF_3')) | ~v1_funct_1(E_274) | ~m1_pre_topc(C_277, '#skF_5') | v2_struct_0(C_277) | ~r2_hidden('#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(E_274, '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_46, c_36, c_312])).
% 2.72/1.39  tff(c_316, plain, (![C_277]: (r2_funct_2(u1_struct_0(C_277), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', C_277), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0(C_277), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(C_277, '#skF_5') | v2_struct_0(C_277) | ~r2_hidden('#skF_1'('#skF_7', '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_5', C_277, '#skF_6'), u1_struct_0('#skF_5')))), inference(reflexivity, [status(thm), theory('equality')], [c_313])).
% 2.72/1.39  tff(c_320, plain, (![C_281]: (r2_funct_2(u1_struct_0(C_281), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', C_281), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_281), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0(C_281), u1_struct_0('#skF_3')) | ~m1_pre_topc(C_281, '#skF_5') | v2_struct_0(C_281) | ~r2_hidden('#skF_1'('#skF_7', '#skF_3', '#skF_5', C_281, '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_5', C_281, '#skF_6'), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_316])).
% 2.72/1.39  tff(c_322, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4') | ~r2_hidden('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_320])).
% 2.72/1.39  tff(c_325, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_306, c_26, c_22, c_322])).
% 2.72/1.39  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_214, c_325])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 1
% 2.72/1.39  #Sup     : 46
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 3
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 8
% 2.72/1.39  #Demod        : 120
% 2.72/1.39  #Tautology    : 17
% 2.72/1.39  #SimpNegUnit  : 24
% 2.72/1.39  #BackRed      : 2
% 2.72/1.39  
% 2.72/1.39  #Partial instantiations: 0
% 2.72/1.39  #Strategies tried      : 1
% 2.72/1.39  
% 2.72/1.39  Timing (in seconds)
% 2.72/1.39  ----------------------
% 2.72/1.39  Preprocessing        : 0.35
% 2.72/1.39  Parsing              : 0.19
% 2.72/1.39  CNF conversion       : 0.04
% 2.72/1.39  Main loop            : 0.26
% 2.72/1.39  Inferencing          : 0.09
% 2.72/1.39  Reduction            : 0.09
% 2.72/1.39  Demodulation         : 0.06
% 2.72/1.39  BG Simplification    : 0.02
% 2.72/1.39  Subsumption          : 0.05
% 2.72/1.39  Abstraction          : 0.01
% 2.72/1.39  MUC search           : 0.00
% 2.72/1.39  Cooper               : 0.00
% 2.72/1.39  Total                : 0.66
% 2.72/1.39  Index Insertion      : 0.00
% 2.72/1.39  Index Deletion       : 0.00
% 2.72/1.39  Index Matching       : 0.00
% 2.72/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
