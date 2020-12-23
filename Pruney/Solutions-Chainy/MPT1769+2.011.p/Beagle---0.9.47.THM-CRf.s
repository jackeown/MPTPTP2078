%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:19 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  174 (1688 expanded)
%              Number of leaves         :   32 ( 569 expanded)
%              Depth                    :   17
%              Number of atoms          :  602 (10504 expanded)
%              Number of equality atoms :   82 ( 743 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_121,axiom,(
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

tff(f_89,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_18,plain,(
    '#skF_1' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_64,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_69,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_64])).

tff(c_119,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_68,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_42])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_67,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_70,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_38])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_71,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_215,plain,(
    ! [E_219,B_222,C_221,D_223,A_220] :
      ( k3_tmap_1(A_220,B_222,C_221,D_223,E_219) = k2_partfun1(u1_struct_0(C_221),u1_struct_0(B_222),E_219,u1_struct_0(D_223))
      | ~ m1_pre_topc(D_223,C_221)
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_221),u1_struct_0(B_222))))
      | ~ v1_funct_2(E_219,u1_struct_0(C_221),u1_struct_0(B_222))
      | ~ v1_funct_1(E_219)
      | ~ m1_pre_topc(D_223,A_220)
      | ~ m1_pre_topc(C_221,A_220)
      | ~ l1_pre_topc(B_222)
      | ~ v2_pre_topc(B_222)
      | v2_struct_0(B_222)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_219,plain,(
    ! [A_220,D_223] :
      ( k3_tmap_1(A_220,'#skF_2','#skF_4',D_223,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_223))
      | ~ m1_pre_topc(D_223,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_223,A_220)
      | ~ m1_pre_topc('#skF_4',A_220)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_72,c_215])).

tff(c_226,plain,(
    ! [A_220,D_223] :
      ( k3_tmap_1(A_220,'#skF_2','#skF_4',D_223,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_223))
      | ~ m1_pre_topc(D_223,'#skF_4')
      | ~ m1_pre_topc(D_223,A_220)
      | ~ m1_pre_topc('#skF_4',A_220)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_71,c_219])).

tff(c_250,plain,(
    ! [A_226,D_227] :
      ( k3_tmap_1(A_226,'#skF_2','#skF_4',D_227,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_227))
      | ~ m1_pre_topc(D_227,'#skF_4')
      | ~ m1_pre_topc(D_227,A_226)
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_226])).

tff(c_254,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_250])).

tff(c_262,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_70,c_68,c_254])).

tff(c_263,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_262])).

tff(c_192,plain,(
    ! [A_214,B_215,C_216,D_217] :
      ( k2_partfun1(u1_struct_0(A_214),u1_struct_0(B_215),C_216,u1_struct_0(D_217)) = k2_tmap_1(A_214,B_215,C_216,D_217)
      | ~ m1_pre_topc(D_217,A_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),u1_struct_0(B_215))))
      | ~ v1_funct_2(C_216,u1_struct_0(A_214),u1_struct_0(B_215))
      | ~ v1_funct_1(C_216)
      | ~ l1_pre_topc(B_215)
      | ~ v2_pre_topc(B_215)
      | v2_struct_0(B_215)
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_196,plain,(
    ! [D_217] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_217)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_217)
      | ~ m1_pre_topc(D_217,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_192])).

tff(c_203,plain,(
    ! [D_217] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_217)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_217)
      | ~ m1_pre_topc(D_217,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_48,c_46,c_36,c_71,c_196])).

tff(c_204,plain,(
    ! [D_217] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_217)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_217)
      | ~ m1_pre_topc(D_217,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_203])).

tff(c_271,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_204])).

tff(c_278,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_271])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_80,plain,(
    ! [C_188,B_189,A_190] :
      ( v1_xboole_0(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(B_189,A_190)))
      | ~ v1_xboole_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_93,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_24,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_22,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_20,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_16,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_74,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_143,plain,(
    ! [E_211,A_209,F_210,B_207,D_206,C_208] :
      ( F_210 = E_211
      | ~ r1_funct_2(A_209,B_207,C_208,D_206,E_211,F_210)
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(C_208,D_206)))
      | ~ v1_funct_2(F_210,C_208,D_206)
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_207)))
      | ~ v1_funct_2(E_211,A_209,B_207)
      | ~ v1_funct_1(E_211)
      | v1_xboole_0(D_206)
      | v1_xboole_0(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_149,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_143])).

tff(c_162,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_71,c_72,c_24,c_22,c_20,c_149])).

tff(c_163,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_162])).

tff(c_58,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_73,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_58])).

tff(c_121,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_73])).

tff(c_165,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_121])).

tff(c_283,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_165])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_283])).

tff(c_288,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_384,plain,(
    ! [C_252,D_254,A_251,B_253,E_250] :
      ( k3_tmap_1(A_251,B_253,C_252,D_254,E_250) = k2_partfun1(u1_struct_0(C_252),u1_struct_0(B_253),E_250,u1_struct_0(D_254))
      | ~ m1_pre_topc(D_254,C_252)
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252),u1_struct_0(B_253))))
      | ~ v1_funct_2(E_250,u1_struct_0(C_252),u1_struct_0(B_253))
      | ~ v1_funct_1(E_250)
      | ~ m1_pre_topc(D_254,A_251)
      | ~ m1_pre_topc(C_252,A_251)
      | ~ l1_pre_topc(B_253)
      | ~ v2_pre_topc(B_253)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_388,plain,(
    ! [A_251,D_254] :
      ( k3_tmap_1(A_251,'#skF_2','#skF_4',D_254,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_254))
      | ~ m1_pre_topc(D_254,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_254,A_251)
      | ~ m1_pre_topc('#skF_4',A_251)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_72,c_384])).

tff(c_395,plain,(
    ! [A_251,D_254] :
      ( k3_tmap_1(A_251,'#skF_2','#skF_4',D_254,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_254))
      | ~ m1_pre_topc(D_254,'#skF_4')
      | ~ m1_pre_topc(D_254,A_251)
      | ~ m1_pre_topc('#skF_4',A_251)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_71,c_388])).

tff(c_419,plain,(
    ! [A_257,D_258] :
      ( k3_tmap_1(A_257,'#skF_2','#skF_4',D_258,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_258))
      | ~ m1_pre_topc(D_258,'#skF_4')
      | ~ m1_pre_topc(D_258,A_257)
      | ~ m1_pre_topc('#skF_4',A_257)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_395])).

tff(c_423,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_419])).

tff(c_431,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_70,c_68,c_423])).

tff(c_432,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_431])).

tff(c_361,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( k2_partfun1(u1_struct_0(A_245),u1_struct_0(B_246),C_247,u1_struct_0(D_248)) = k2_tmap_1(A_245,B_246,C_247,D_248)
      | ~ m1_pre_topc(D_248,A_245)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245),u1_struct_0(B_246))))
      | ~ v1_funct_2(C_247,u1_struct_0(A_245),u1_struct_0(B_246))
      | ~ v1_funct_1(C_247)
      | ~ l1_pre_topc(B_246)
      | ~ v2_pre_topc(B_246)
      | v2_struct_0(B_246)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_365,plain,(
    ! [D_248] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_248)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_248)
      | ~ m1_pre_topc(D_248,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_361])).

tff(c_372,plain,(
    ! [D_248] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_248)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_248)
      | ~ m1_pre_topc(D_248,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_48,c_46,c_36,c_71,c_365])).

tff(c_373,plain,(
    ! [D_248] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_248)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_248)
      | ~ m1_pre_topc(D_248,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_372])).

tff(c_440,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_373])).

tff(c_447,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_440])).

tff(c_313,plain,(
    ! [E_244,B_240,C_241,D_239,F_243,A_242] :
      ( F_243 = E_244
      | ~ r1_funct_2(A_242,B_240,C_241,D_239,E_244,F_243)
      | ~ m1_subset_1(F_243,k1_zfmisc_1(k2_zfmisc_1(C_241,D_239)))
      | ~ v1_funct_2(F_243,C_241,D_239)
      | ~ v1_funct_1(F_243)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_240)))
      | ~ v1_funct_2(E_244,A_242,B_240)
      | ~ v1_funct_1(E_244)
      | v1_xboole_0(D_239)
      | v1_xboole_0(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_321,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_313])).

tff(c_339,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_71,c_72,c_24,c_22,c_20,c_321])).

tff(c_340,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_339])).

tff(c_287,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_342,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_287])).

tff(c_452,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_342])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_452])).

tff(c_455,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_456,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_475,plain,(
    ! [A_259] :
      ( A_259 = '#skF_6'
      | ~ v1_xboole_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_485,plain,(
    u1_struct_0('#skF_2') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_456,c_475])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_80])).

tff(c_512,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_485,c_92])).

tff(c_459,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_518,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_512,c_459])).

tff(c_91,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_460,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_460])).

tff(c_466,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_486,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_466,c_475])).

tff(c_572,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_485,c_485,c_486,c_69])).

tff(c_573,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_572])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_503,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_71])).

tff(c_537,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_503])).

tff(c_491,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_20])).

tff(c_545,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_491])).

tff(c_642,plain,(
    ! [B_293,E_290,A_291,C_292,D_294] :
      ( k3_tmap_1(A_291,B_293,C_292,D_294,E_290) = k2_partfun1(u1_struct_0(C_292),u1_struct_0(B_293),E_290,u1_struct_0(D_294))
      | ~ m1_pre_topc(D_294,C_292)
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292),u1_struct_0(B_293))))
      | ~ v1_funct_2(E_290,u1_struct_0(C_292),u1_struct_0(B_293))
      | ~ v1_funct_1(E_290)
      | ~ m1_pre_topc(D_294,A_291)
      | ~ m1_pre_topc(C_292,A_291)
      | ~ l1_pre_topc(B_293)
      | ~ v2_pre_topc(B_293)
      | v2_struct_0(B_293)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_646,plain,(
    ! [A_291,C_292,D_294,E_290] :
      ( k3_tmap_1(A_291,'#skF_2',C_292,D_294,E_290) = k2_partfun1(u1_struct_0(C_292),u1_struct_0('#skF_2'),E_290,u1_struct_0(D_294))
      | ~ m1_pre_topc(D_294,C_292)
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292),'#skF_6')))
      | ~ v1_funct_2(E_290,u1_struct_0(C_292),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_290)
      | ~ m1_pre_topc(D_294,A_291)
      | ~ m1_pre_topc(C_292,A_291)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_642])).

tff(c_649,plain,(
    ! [A_291,C_292,D_294,E_290] :
      ( k3_tmap_1(A_291,'#skF_2',C_292,D_294,E_290) = k2_partfun1(u1_struct_0(C_292),'#skF_6',E_290,u1_struct_0(D_294))
      | ~ m1_pre_topc(D_294,C_292)
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292),'#skF_6')))
      | ~ v1_funct_2(E_290,u1_struct_0(C_292),'#skF_6')
      | ~ v1_funct_1(E_290)
      | ~ m1_pre_topc(D_294,A_291)
      | ~ m1_pre_topc(C_292,A_291)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_485,c_485,c_646])).

tff(c_653,plain,(
    ! [A_295,C_296,D_297,E_298] :
      ( k3_tmap_1(A_295,'#skF_2',C_296,D_297,E_298) = k2_partfun1(u1_struct_0(C_296),'#skF_6',E_298,u1_struct_0(D_297))
      | ~ m1_pre_topc(D_297,C_296)
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_296),'#skF_6')))
      | ~ v1_funct_2(E_298,u1_struct_0(C_296),'#skF_6')
      | ~ v1_funct_1(E_298)
      | ~ m1_pre_topc(D_297,A_295)
      | ~ m1_pre_topc(C_296,A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_649])).

tff(c_655,plain,(
    ! [A_295,D_297] :
      ( k3_tmap_1(A_295,'#skF_2','#skF_4',D_297,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_297))
      | ~ m1_pre_topc(D_297,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_297,A_295)
      | ~ m1_pre_topc('#skF_4',A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_545,c_653])).

tff(c_695,plain,(
    ! [A_305,D_306] :
      ( k3_tmap_1(A_305,'#skF_2','#skF_4',D_306,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_306))
      | ~ m1_pre_topc(D_306,'#skF_4')
      | ~ m1_pre_topc(D_306,A_305)
      | ~ m1_pre_topc('#skF_4',A_305)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_537,c_655])).

tff(c_699,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_695])).

tff(c_707,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_70,c_68,c_699])).

tff(c_708,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_707])).

tff(c_594,plain,(
    ! [A_277,B_278,C_279,D_280] :
      ( k2_partfun1(u1_struct_0(A_277),u1_struct_0(B_278),C_279,u1_struct_0(D_280)) = k2_tmap_1(A_277,B_278,C_279,D_280)
      | ~ m1_pre_topc(D_280,A_277)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277),u1_struct_0(B_278))))
      | ~ v1_funct_2(C_279,u1_struct_0(A_277),u1_struct_0(B_278))
      | ~ v1_funct_1(C_279)
      | ~ l1_pre_topc(B_278)
      | ~ v2_pre_topc(B_278)
      | v2_struct_0(B_278)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_598,plain,(
    ! [A_277,C_279,D_280] :
      ( k2_partfun1(u1_struct_0(A_277),u1_struct_0('#skF_2'),C_279,u1_struct_0(D_280)) = k2_tmap_1(A_277,'#skF_2',C_279,D_280)
      | ~ m1_pre_topc(D_280,A_277)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277),'#skF_6')))
      | ~ v1_funct_2(C_279,u1_struct_0(A_277),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_279)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_594])).

tff(c_603,plain,(
    ! [A_277,C_279,D_280] :
      ( k2_partfun1(u1_struct_0(A_277),'#skF_6',C_279,u1_struct_0(D_280)) = k2_tmap_1(A_277,'#skF_2',C_279,D_280)
      | ~ m1_pre_topc(D_280,A_277)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277),'#skF_6')))
      | ~ v1_funct_2(C_279,u1_struct_0(A_277),'#skF_6')
      | ~ v1_funct_1(C_279)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_485,c_485,c_598])).

tff(c_612,plain,(
    ! [A_286,C_287,D_288] :
      ( k2_partfun1(u1_struct_0(A_286),'#skF_6',C_287,u1_struct_0(D_288)) = k2_tmap_1(A_286,'#skF_2',C_287,D_288)
      | ~ m1_pre_topc(D_288,A_286)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_286),'#skF_6')))
      | ~ v1_funct_2(C_287,u1_struct_0(A_286),'#skF_6')
      | ~ v1_funct_1(C_287)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_603])).

tff(c_614,plain,(
    ! [D_288] :
      ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_288)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_288)
      | ~ m1_pre_topc(D_288,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_545,c_612])).

tff(c_621,plain,(
    ! [D_288] :
      ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_288)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_288)
      | ~ m1_pre_topc(D_288,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_30,c_537,c_614])).

tff(c_622,plain,(
    ! [D_288] :
      ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_288)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_288)
      | ~ m1_pre_topc(D_288,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_621])).

tff(c_716,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_622])).

tff(c_723,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_716])).

tff(c_574,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_486,c_518,c_485,c_73])).

tff(c_575,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_742,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_575])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_742])).

tff(c_746,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_746])).

tff(c_751,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_572])).

tff(c_821,plain,(
    ! [D_335,B_334,E_331,C_333,A_332] :
      ( k3_tmap_1(A_332,B_334,C_333,D_335,E_331) = k2_partfun1(u1_struct_0(C_333),u1_struct_0(B_334),E_331,u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,C_333)
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_333),u1_struct_0(B_334))))
      | ~ v1_funct_2(E_331,u1_struct_0(C_333),u1_struct_0(B_334))
      | ~ v1_funct_1(E_331)
      | ~ m1_pre_topc(D_335,A_332)
      | ~ m1_pre_topc(C_333,A_332)
      | ~ l1_pre_topc(B_334)
      | ~ v2_pre_topc(B_334)
      | v2_struct_0(B_334)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_825,plain,(
    ! [A_332,C_333,D_335,E_331] :
      ( k3_tmap_1(A_332,'#skF_2',C_333,D_335,E_331) = k2_partfun1(u1_struct_0(C_333),u1_struct_0('#skF_2'),E_331,u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,C_333)
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_333),'#skF_6')))
      | ~ v1_funct_2(E_331,u1_struct_0(C_333),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_331)
      | ~ m1_pre_topc(D_335,A_332)
      | ~ m1_pre_topc(C_333,A_332)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_821])).

tff(c_828,plain,(
    ! [A_332,C_333,D_335,E_331] :
      ( k3_tmap_1(A_332,'#skF_2',C_333,D_335,E_331) = k2_partfun1(u1_struct_0(C_333),'#skF_6',E_331,u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,C_333)
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_333),'#skF_6')))
      | ~ v1_funct_2(E_331,u1_struct_0(C_333),'#skF_6')
      | ~ v1_funct_1(E_331)
      | ~ m1_pre_topc(D_335,A_332)
      | ~ m1_pre_topc(C_333,A_332)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_485,c_485,c_825])).

tff(c_831,plain,(
    ! [A_336,C_337,D_338,E_339] :
      ( k3_tmap_1(A_336,'#skF_2',C_337,D_338,E_339) = k2_partfun1(u1_struct_0(C_337),'#skF_6',E_339,u1_struct_0(D_338))
      | ~ m1_pre_topc(D_338,C_337)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_337),'#skF_6')))
      | ~ v1_funct_2(E_339,u1_struct_0(C_337),'#skF_6')
      | ~ v1_funct_1(E_339)
      | ~ m1_pre_topc(D_338,A_336)
      | ~ m1_pre_topc(C_337,A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_828])).

tff(c_833,plain,(
    ! [A_336,D_338] :
      ( k3_tmap_1(A_336,'#skF_2','#skF_4',D_338,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_338))
      | ~ m1_pre_topc(D_338,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_338,A_336)
      | ~ m1_pre_topc('#skF_4',A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_545,c_831])).

tff(c_845,plain,(
    ! [A_340,D_341] :
      ( k3_tmap_1(A_340,'#skF_2','#skF_4',D_341,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_341))
      | ~ m1_pre_topc(D_341,'#skF_4')
      | ~ m1_pre_topc(D_341,A_340)
      | ~ m1_pre_topc('#skF_4',A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_537,c_833])).

tff(c_849,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_845])).

tff(c_857,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_70,c_68,c_849])).

tff(c_858,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_857])).

tff(c_772,plain,(
    ! [A_318,B_319,C_320,D_321] :
      ( k2_partfun1(u1_struct_0(A_318),u1_struct_0(B_319),C_320,u1_struct_0(D_321)) = k2_tmap_1(A_318,B_319,C_320,D_321)
      | ~ m1_pre_topc(D_321,A_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318),u1_struct_0(B_319))))
      | ~ v1_funct_2(C_320,u1_struct_0(A_318),u1_struct_0(B_319))
      | ~ v1_funct_1(C_320)
      | ~ l1_pre_topc(B_319)
      | ~ v2_pre_topc(B_319)
      | v2_struct_0(B_319)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_776,plain,(
    ! [A_318,C_320,D_321] :
      ( k2_partfun1(u1_struct_0(A_318),u1_struct_0('#skF_2'),C_320,u1_struct_0(D_321)) = k2_tmap_1(A_318,'#skF_2',C_320,D_321)
      | ~ m1_pre_topc(D_321,A_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318),'#skF_6')))
      | ~ v1_funct_2(C_320,u1_struct_0(A_318),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_320)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_772])).

tff(c_781,plain,(
    ! [A_318,C_320,D_321] :
      ( k2_partfun1(u1_struct_0(A_318),'#skF_6',C_320,u1_struct_0(D_321)) = k2_tmap_1(A_318,'#skF_2',C_320,D_321)
      | ~ m1_pre_topc(D_321,A_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318),'#skF_6')))
      | ~ v1_funct_2(C_320,u1_struct_0(A_318),'#skF_6')
      | ~ v1_funct_1(C_320)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_485,c_485,c_776])).

tff(c_790,plain,(
    ! [A_327,C_328,D_329] :
      ( k2_partfun1(u1_struct_0(A_327),'#skF_6',C_328,u1_struct_0(D_329)) = k2_tmap_1(A_327,'#skF_2',C_328,D_329)
      | ~ m1_pre_topc(D_329,A_327)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_327),'#skF_6')))
      | ~ v1_funct_2(C_328,u1_struct_0(A_327),'#skF_6')
      | ~ v1_funct_1(C_328)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_781])).

tff(c_792,plain,(
    ! [D_329] :
      ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_329)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_329)
      | ~ m1_pre_topc(D_329,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_545,c_790])).

tff(c_799,plain,(
    ! [D_329] :
      ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_329)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_329)
      | ~ m1_pre_topc(D_329,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_30,c_537,c_792])).

tff(c_800,plain,(
    ! [D_329] :
      ( k2_partfun1(u1_struct_0('#skF_4'),'#skF_6','#skF_6',u1_struct_0(D_329)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_329)
      | ~ m1_pre_topc(D_329,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_799])).

tff(c_866,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_800])).

tff(c_873,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_866])).

tff(c_750,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_572])).

tff(c_878,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_750])).

tff(c_880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_751,c_878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:17:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.55  
% 3.54/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.55  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.54/1.55  
% 3.54/1.55  %Foreground sorts:
% 3.54/1.55  
% 3.54/1.55  
% 3.54/1.55  %Background operators:
% 3.54/1.55  
% 3.54/1.55  
% 3.54/1.55  %Foreground operators:
% 3.54/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.54/1.55  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.55  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.54/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.54/1.55  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.54/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.55  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.54/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.55  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.54/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.55  
% 3.65/1.58  tff(f_190, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 3.65/1.58  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.65/1.58  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.65/1.58  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.65/1.58  tff(f_62, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.65/1.58  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.65/1.58  tff(c_18, plain, ('#skF_1'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_64, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_69, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_64])).
% 3.65/1.58  tff(c_119, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_69])).
% 3.65/1.58  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_68, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_42])).
% 3.65/1.58  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_54])).
% 3.65/1.58  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_67, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 3.65/1.58  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_70, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_38])).
% 3.65/1.58  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_71, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_34])).
% 3.65/1.58  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 3.65/1.58  tff(c_215, plain, (![E_219, B_222, C_221, D_223, A_220]: (k3_tmap_1(A_220, B_222, C_221, D_223, E_219)=k2_partfun1(u1_struct_0(C_221), u1_struct_0(B_222), E_219, u1_struct_0(D_223)) | ~m1_pre_topc(D_223, C_221) | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_221), u1_struct_0(B_222)))) | ~v1_funct_2(E_219, u1_struct_0(C_221), u1_struct_0(B_222)) | ~v1_funct_1(E_219) | ~m1_pre_topc(D_223, A_220) | ~m1_pre_topc(C_221, A_220) | ~l1_pre_topc(B_222) | ~v2_pre_topc(B_222) | v2_struct_0(B_222) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_219, plain, (![A_220, D_223]: (k3_tmap_1(A_220, '#skF_2', '#skF_4', D_223, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_223)) | ~m1_pre_topc(D_223, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_223, A_220) | ~m1_pre_topc('#skF_4', A_220) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(resolution, [status(thm)], [c_72, c_215])).
% 3.65/1.58  tff(c_226, plain, (![A_220, D_223]: (k3_tmap_1(A_220, '#skF_2', '#skF_4', D_223, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_223)) | ~m1_pre_topc(D_223, '#skF_4') | ~m1_pre_topc(D_223, A_220) | ~m1_pre_topc('#skF_4', A_220) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_71, c_219])).
% 3.65/1.58  tff(c_250, plain, (![A_226, D_227]: (k3_tmap_1(A_226, '#skF_2', '#skF_4', D_227, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_227)) | ~m1_pre_topc(D_227, '#skF_4') | ~m1_pre_topc(D_227, A_226) | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(negUnitSimplification, [status(thm)], [c_50, c_226])).
% 3.65/1.58  tff(c_254, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_250])).
% 3.65/1.58  tff(c_262, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_70, c_68, c_254])).
% 3.65/1.58  tff(c_263, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_262])).
% 3.65/1.58  tff(c_192, plain, (![A_214, B_215, C_216, D_217]: (k2_partfun1(u1_struct_0(A_214), u1_struct_0(B_215), C_216, u1_struct_0(D_217))=k2_tmap_1(A_214, B_215, C_216, D_217) | ~m1_pre_topc(D_217, A_214) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214), u1_struct_0(B_215)))) | ~v1_funct_2(C_216, u1_struct_0(A_214), u1_struct_0(B_215)) | ~v1_funct_1(C_216) | ~l1_pre_topc(B_215) | ~v2_pre_topc(B_215) | v2_struct_0(B_215) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.65/1.58  tff(c_196, plain, (![D_217]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_217))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_217) | ~m1_pre_topc(D_217, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_192])).
% 3.65/1.58  tff(c_203, plain, (![D_217]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_217))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_217) | ~m1_pre_topc(D_217, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_48, c_46, c_36, c_71, c_196])).
% 3.65/1.58  tff(c_204, plain, (![D_217]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_217))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_217) | ~m1_pre_topc(D_217, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_203])).
% 3.65/1.58  tff(c_271, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_263, c_204])).
% 3.65/1.58  tff(c_278, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_271])).
% 3.65/1.58  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_80, plain, (![C_188, B_189, A_190]: (v1_xboole_0(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(B_189, A_190))) | ~v1_xboole_0(A_190))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.65/1.58  tff(c_90, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_80])).
% 3.65/1.58  tff(c_93, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_90])).
% 3.65/1.58  tff(c_24, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_22, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_20, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_16, plain, (r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_74, plain, (r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 3.65/1.58  tff(c_143, plain, (![E_211, A_209, F_210, B_207, D_206, C_208]: (F_210=E_211 | ~r1_funct_2(A_209, B_207, C_208, D_206, E_211, F_210) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(C_208, D_206))) | ~v1_funct_2(F_210, C_208, D_206) | ~v1_funct_1(F_210) | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_207))) | ~v1_funct_2(E_211, A_209, B_207) | ~v1_funct_1(E_211) | v1_xboole_0(D_206) | v1_xboole_0(B_207))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.65/1.58  tff(c_149, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_143])).
% 3.65/1.58  tff(c_162, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_71, c_72, c_24, c_22, c_20, c_149])).
% 3.65/1.58  tff(c_163, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_93, c_162])).
% 3.65/1.58  tff(c_58, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_73, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_58])).
% 3.65/1.58  tff(c_121, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_73])).
% 3.65/1.58  tff(c_165, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_121])).
% 3.65/1.58  tff(c_283, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_165])).
% 3.65/1.58  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_283])).
% 3.65/1.58  tff(c_288, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.65/1.58  tff(c_384, plain, (![C_252, D_254, A_251, B_253, E_250]: (k3_tmap_1(A_251, B_253, C_252, D_254, E_250)=k2_partfun1(u1_struct_0(C_252), u1_struct_0(B_253), E_250, u1_struct_0(D_254)) | ~m1_pre_topc(D_254, C_252) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252), u1_struct_0(B_253)))) | ~v1_funct_2(E_250, u1_struct_0(C_252), u1_struct_0(B_253)) | ~v1_funct_1(E_250) | ~m1_pre_topc(D_254, A_251) | ~m1_pre_topc(C_252, A_251) | ~l1_pre_topc(B_253) | ~v2_pre_topc(B_253) | v2_struct_0(B_253) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_388, plain, (![A_251, D_254]: (k3_tmap_1(A_251, '#skF_2', '#skF_4', D_254, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_254)) | ~m1_pre_topc(D_254, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_254, A_251) | ~m1_pre_topc('#skF_4', A_251) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_72, c_384])).
% 3.65/1.58  tff(c_395, plain, (![A_251, D_254]: (k3_tmap_1(A_251, '#skF_2', '#skF_4', D_254, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_254)) | ~m1_pre_topc(D_254, '#skF_4') | ~m1_pre_topc(D_254, A_251) | ~m1_pre_topc('#skF_4', A_251) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_71, c_388])).
% 3.65/1.58  tff(c_419, plain, (![A_257, D_258]: (k3_tmap_1(A_257, '#skF_2', '#skF_4', D_258, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_258)) | ~m1_pre_topc(D_258, '#skF_4') | ~m1_pre_topc(D_258, A_257) | ~m1_pre_topc('#skF_4', A_257) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(negUnitSimplification, [status(thm)], [c_50, c_395])).
% 3.65/1.58  tff(c_423, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_419])).
% 3.65/1.58  tff(c_431, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_70, c_68, c_423])).
% 3.65/1.58  tff(c_432, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_431])).
% 3.65/1.58  tff(c_361, plain, (![A_245, B_246, C_247, D_248]: (k2_partfun1(u1_struct_0(A_245), u1_struct_0(B_246), C_247, u1_struct_0(D_248))=k2_tmap_1(A_245, B_246, C_247, D_248) | ~m1_pre_topc(D_248, A_245) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245), u1_struct_0(B_246)))) | ~v1_funct_2(C_247, u1_struct_0(A_245), u1_struct_0(B_246)) | ~v1_funct_1(C_247) | ~l1_pre_topc(B_246) | ~v2_pre_topc(B_246) | v2_struct_0(B_246) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.65/1.58  tff(c_365, plain, (![D_248]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_248))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_248) | ~m1_pre_topc(D_248, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_361])).
% 3.65/1.58  tff(c_372, plain, (![D_248]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_248))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_248) | ~m1_pre_topc(D_248, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_48, c_46, c_36, c_71, c_365])).
% 3.65/1.58  tff(c_373, plain, (![D_248]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_248))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_248) | ~m1_pre_topc(D_248, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_372])).
% 3.65/1.58  tff(c_440, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_432, c_373])).
% 3.65/1.58  tff(c_447, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_440])).
% 3.65/1.58  tff(c_313, plain, (![E_244, B_240, C_241, D_239, F_243, A_242]: (F_243=E_244 | ~r1_funct_2(A_242, B_240, C_241, D_239, E_244, F_243) | ~m1_subset_1(F_243, k1_zfmisc_1(k2_zfmisc_1(C_241, D_239))) | ~v1_funct_2(F_243, C_241, D_239) | ~v1_funct_1(F_243) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_240))) | ~v1_funct_2(E_244, A_242, B_240) | ~v1_funct_1(E_244) | v1_xboole_0(D_239) | v1_xboole_0(B_240))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.65/1.58  tff(c_321, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_313])).
% 3.65/1.58  tff(c_339, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_71, c_72, c_24, c_22, c_20, c_321])).
% 3.65/1.58  tff(c_340, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_93, c_339])).
% 3.65/1.58  tff(c_287, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.65/1.58  tff(c_342, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_287])).
% 3.65/1.58  tff(c_452, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_447, c_342])).
% 3.65/1.58  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_452])).
% 3.65/1.58  tff(c_455, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 3.65/1.58  tff(c_456, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_90])).
% 3.65/1.58  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/1.58  tff(c_475, plain, (![A_259]: (A_259='#skF_6' | ~v1_xboole_0(A_259))), inference(resolution, [status(thm)], [c_455, c_2])).
% 3.65/1.58  tff(c_485, plain, (u1_struct_0('#skF_2')='#skF_6'), inference(resolution, [status(thm)], [c_456, c_475])).
% 3.65/1.58  tff(c_92, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_80])).
% 3.65/1.58  tff(c_512, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_455, c_485, c_92])).
% 3.65/1.58  tff(c_459, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_455, c_2])).
% 3.65/1.58  tff(c_518, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_512, c_459])).
% 3.65/1.58  tff(c_91, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_80])).
% 3.65/1.58  tff(c_460, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_91])).
% 3.65/1.58  tff(c_465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_460])).
% 3.65/1.58  tff(c_466, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_91])).
% 3.65/1.58  tff(c_486, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_466, c_475])).
% 3.65/1.58  tff(c_572, plain, (r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_518, c_485, c_485, c_486, c_69])).
% 3.65/1.58  tff(c_573, plain, (r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_572])).
% 3.65/1.58  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.65/1.58  tff(c_503, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_71])).
% 3.65/1.58  tff(c_537, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_518, c_503])).
% 3.65/1.58  tff(c_491, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_20])).
% 3.65/1.58  tff(c_545, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_491])).
% 3.65/1.58  tff(c_642, plain, (![B_293, E_290, A_291, C_292, D_294]: (k3_tmap_1(A_291, B_293, C_292, D_294, E_290)=k2_partfun1(u1_struct_0(C_292), u1_struct_0(B_293), E_290, u1_struct_0(D_294)) | ~m1_pre_topc(D_294, C_292) | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292), u1_struct_0(B_293)))) | ~v1_funct_2(E_290, u1_struct_0(C_292), u1_struct_0(B_293)) | ~v1_funct_1(E_290) | ~m1_pre_topc(D_294, A_291) | ~m1_pre_topc(C_292, A_291) | ~l1_pre_topc(B_293) | ~v2_pre_topc(B_293) | v2_struct_0(B_293) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_646, plain, (![A_291, C_292, D_294, E_290]: (k3_tmap_1(A_291, '#skF_2', C_292, D_294, E_290)=k2_partfun1(u1_struct_0(C_292), u1_struct_0('#skF_2'), E_290, u1_struct_0(D_294)) | ~m1_pre_topc(D_294, C_292) | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292), '#skF_6'))) | ~v1_funct_2(E_290, u1_struct_0(C_292), u1_struct_0('#skF_2')) | ~v1_funct_1(E_290) | ~m1_pre_topc(D_294, A_291) | ~m1_pre_topc(C_292, A_291) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(superposition, [status(thm), theory('equality')], [c_485, c_642])).
% 3.65/1.58  tff(c_649, plain, (![A_291, C_292, D_294, E_290]: (k3_tmap_1(A_291, '#skF_2', C_292, D_294, E_290)=k2_partfun1(u1_struct_0(C_292), '#skF_6', E_290, u1_struct_0(D_294)) | ~m1_pre_topc(D_294, C_292) | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292), '#skF_6'))) | ~v1_funct_2(E_290, u1_struct_0(C_292), '#skF_6') | ~v1_funct_1(E_290) | ~m1_pre_topc(D_294, A_291) | ~m1_pre_topc(C_292, A_291) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_485, c_485, c_646])).
% 3.65/1.58  tff(c_653, plain, (![A_295, C_296, D_297, E_298]: (k3_tmap_1(A_295, '#skF_2', C_296, D_297, E_298)=k2_partfun1(u1_struct_0(C_296), '#skF_6', E_298, u1_struct_0(D_297)) | ~m1_pre_topc(D_297, C_296) | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_296), '#skF_6'))) | ~v1_funct_2(E_298, u1_struct_0(C_296), '#skF_6') | ~v1_funct_1(E_298) | ~m1_pre_topc(D_297, A_295) | ~m1_pre_topc(C_296, A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(negUnitSimplification, [status(thm)], [c_50, c_649])).
% 3.65/1.58  tff(c_655, plain, (![A_295, D_297]: (k3_tmap_1(A_295, '#skF_2', '#skF_4', D_297, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_297)) | ~m1_pre_topc(D_297, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_297, A_295) | ~m1_pre_topc('#skF_4', A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(resolution, [status(thm)], [c_545, c_653])).
% 3.65/1.58  tff(c_695, plain, (![A_305, D_306]: (k3_tmap_1(A_305, '#skF_2', '#skF_4', D_306, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_306)) | ~m1_pre_topc(D_306, '#skF_4') | ~m1_pre_topc(D_306, A_305) | ~m1_pre_topc('#skF_4', A_305) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_537, c_655])).
% 3.65/1.58  tff(c_699, plain, (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_695])).
% 3.65/1.58  tff(c_707, plain, (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_70, c_68, c_699])).
% 3.65/1.58  tff(c_708, plain, (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_707])).
% 3.65/1.58  tff(c_594, plain, (![A_277, B_278, C_279, D_280]: (k2_partfun1(u1_struct_0(A_277), u1_struct_0(B_278), C_279, u1_struct_0(D_280))=k2_tmap_1(A_277, B_278, C_279, D_280) | ~m1_pre_topc(D_280, A_277) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277), u1_struct_0(B_278)))) | ~v1_funct_2(C_279, u1_struct_0(A_277), u1_struct_0(B_278)) | ~v1_funct_1(C_279) | ~l1_pre_topc(B_278) | ~v2_pre_topc(B_278) | v2_struct_0(B_278) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.65/1.58  tff(c_598, plain, (![A_277, C_279, D_280]: (k2_partfun1(u1_struct_0(A_277), u1_struct_0('#skF_2'), C_279, u1_struct_0(D_280))=k2_tmap_1(A_277, '#skF_2', C_279, D_280) | ~m1_pre_topc(D_280, A_277) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277), '#skF_6'))) | ~v1_funct_2(C_279, u1_struct_0(A_277), u1_struct_0('#skF_2')) | ~v1_funct_1(C_279) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(superposition, [status(thm), theory('equality')], [c_485, c_594])).
% 3.65/1.58  tff(c_603, plain, (![A_277, C_279, D_280]: (k2_partfun1(u1_struct_0(A_277), '#skF_6', C_279, u1_struct_0(D_280))=k2_tmap_1(A_277, '#skF_2', C_279, D_280) | ~m1_pre_topc(D_280, A_277) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277), '#skF_6'))) | ~v1_funct_2(C_279, u1_struct_0(A_277), '#skF_6') | ~v1_funct_1(C_279) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_485, c_485, c_598])).
% 3.65/1.58  tff(c_612, plain, (![A_286, C_287, D_288]: (k2_partfun1(u1_struct_0(A_286), '#skF_6', C_287, u1_struct_0(D_288))=k2_tmap_1(A_286, '#skF_2', C_287, D_288) | ~m1_pre_topc(D_288, A_286) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_286), '#skF_6'))) | ~v1_funct_2(C_287, u1_struct_0(A_286), '#skF_6') | ~v1_funct_1(C_287) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(negUnitSimplification, [status(thm)], [c_50, c_603])).
% 3.65/1.58  tff(c_614, plain, (![D_288]: (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_288))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_288) | ~m1_pre_topc(D_288, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), '#skF_6') | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_545, c_612])).
% 3.65/1.58  tff(c_621, plain, (![D_288]: (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_288))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_288) | ~m1_pre_topc(D_288, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_30, c_537, c_614])).
% 3.65/1.58  tff(c_622, plain, (![D_288]: (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_288))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_288) | ~m1_pre_topc(D_288, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_621])).
% 3.65/1.58  tff(c_716, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_708, c_622])).
% 3.65/1.58  tff(c_723, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_716])).
% 3.65/1.58  tff(c_574, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_486, c_518, c_485, c_73])).
% 3.65/1.58  tff(c_575, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_574])).
% 3.65/1.58  tff(c_742, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_723, c_575])).
% 3.65/1.58  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_573, c_742])).
% 3.65/1.58  tff(c_746, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_574])).
% 3.65/1.58  tff(c_749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_573, c_746])).
% 3.65/1.58  tff(c_751, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_572])).
% 3.65/1.58  tff(c_821, plain, (![D_335, B_334, E_331, C_333, A_332]: (k3_tmap_1(A_332, B_334, C_333, D_335, E_331)=k2_partfun1(u1_struct_0(C_333), u1_struct_0(B_334), E_331, u1_struct_0(D_335)) | ~m1_pre_topc(D_335, C_333) | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_333), u1_struct_0(B_334)))) | ~v1_funct_2(E_331, u1_struct_0(C_333), u1_struct_0(B_334)) | ~v1_funct_1(E_331) | ~m1_pre_topc(D_335, A_332) | ~m1_pre_topc(C_333, A_332) | ~l1_pre_topc(B_334) | ~v2_pre_topc(B_334) | v2_struct_0(B_334) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_825, plain, (![A_332, C_333, D_335, E_331]: (k3_tmap_1(A_332, '#skF_2', C_333, D_335, E_331)=k2_partfun1(u1_struct_0(C_333), u1_struct_0('#skF_2'), E_331, u1_struct_0(D_335)) | ~m1_pre_topc(D_335, C_333) | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_333), '#skF_6'))) | ~v1_funct_2(E_331, u1_struct_0(C_333), u1_struct_0('#skF_2')) | ~v1_funct_1(E_331) | ~m1_pre_topc(D_335, A_332) | ~m1_pre_topc(C_333, A_332) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(superposition, [status(thm), theory('equality')], [c_485, c_821])).
% 3.65/1.58  tff(c_828, plain, (![A_332, C_333, D_335, E_331]: (k3_tmap_1(A_332, '#skF_2', C_333, D_335, E_331)=k2_partfun1(u1_struct_0(C_333), '#skF_6', E_331, u1_struct_0(D_335)) | ~m1_pre_topc(D_335, C_333) | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_333), '#skF_6'))) | ~v1_funct_2(E_331, u1_struct_0(C_333), '#skF_6') | ~v1_funct_1(E_331) | ~m1_pre_topc(D_335, A_332) | ~m1_pre_topc(C_333, A_332) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_485, c_485, c_825])).
% 3.65/1.58  tff(c_831, plain, (![A_336, C_337, D_338, E_339]: (k3_tmap_1(A_336, '#skF_2', C_337, D_338, E_339)=k2_partfun1(u1_struct_0(C_337), '#skF_6', E_339, u1_struct_0(D_338)) | ~m1_pre_topc(D_338, C_337) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_337), '#skF_6'))) | ~v1_funct_2(E_339, u1_struct_0(C_337), '#skF_6') | ~v1_funct_1(E_339) | ~m1_pre_topc(D_338, A_336) | ~m1_pre_topc(C_337, A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(negUnitSimplification, [status(thm)], [c_50, c_828])).
% 3.65/1.58  tff(c_833, plain, (![A_336, D_338]: (k3_tmap_1(A_336, '#skF_2', '#skF_4', D_338, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_338)) | ~m1_pre_topc(D_338, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_338, A_336) | ~m1_pre_topc('#skF_4', A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_545, c_831])).
% 3.65/1.58  tff(c_845, plain, (![A_340, D_341]: (k3_tmap_1(A_340, '#skF_2', '#skF_4', D_341, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_341)) | ~m1_pre_topc(D_341, '#skF_4') | ~m1_pre_topc(D_341, A_340) | ~m1_pre_topc('#skF_4', A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_537, c_833])).
% 3.65/1.58  tff(c_849, plain, (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_845])).
% 3.65/1.58  tff(c_857, plain, (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_70, c_68, c_849])).
% 3.65/1.58  tff(c_858, plain, (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_857])).
% 3.65/1.58  tff(c_772, plain, (![A_318, B_319, C_320, D_321]: (k2_partfun1(u1_struct_0(A_318), u1_struct_0(B_319), C_320, u1_struct_0(D_321))=k2_tmap_1(A_318, B_319, C_320, D_321) | ~m1_pre_topc(D_321, A_318) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318), u1_struct_0(B_319)))) | ~v1_funct_2(C_320, u1_struct_0(A_318), u1_struct_0(B_319)) | ~v1_funct_1(C_320) | ~l1_pre_topc(B_319) | ~v2_pre_topc(B_319) | v2_struct_0(B_319) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.65/1.58  tff(c_776, plain, (![A_318, C_320, D_321]: (k2_partfun1(u1_struct_0(A_318), u1_struct_0('#skF_2'), C_320, u1_struct_0(D_321))=k2_tmap_1(A_318, '#skF_2', C_320, D_321) | ~m1_pre_topc(D_321, A_318) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318), '#skF_6'))) | ~v1_funct_2(C_320, u1_struct_0(A_318), u1_struct_0('#skF_2')) | ~v1_funct_1(C_320) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(superposition, [status(thm), theory('equality')], [c_485, c_772])).
% 3.65/1.58  tff(c_781, plain, (![A_318, C_320, D_321]: (k2_partfun1(u1_struct_0(A_318), '#skF_6', C_320, u1_struct_0(D_321))=k2_tmap_1(A_318, '#skF_2', C_320, D_321) | ~m1_pre_topc(D_321, A_318) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318), '#skF_6'))) | ~v1_funct_2(C_320, u1_struct_0(A_318), '#skF_6') | ~v1_funct_1(C_320) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_485, c_485, c_776])).
% 3.65/1.58  tff(c_790, plain, (![A_327, C_328, D_329]: (k2_partfun1(u1_struct_0(A_327), '#skF_6', C_328, u1_struct_0(D_329))=k2_tmap_1(A_327, '#skF_2', C_328, D_329) | ~m1_pre_topc(D_329, A_327) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_327), '#skF_6'))) | ~v1_funct_2(C_328, u1_struct_0(A_327), '#skF_6') | ~v1_funct_1(C_328) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(negUnitSimplification, [status(thm)], [c_50, c_781])).
% 3.65/1.58  tff(c_792, plain, (![D_329]: (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_329))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_329) | ~m1_pre_topc(D_329, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), '#skF_6') | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_545, c_790])).
% 3.65/1.58  tff(c_799, plain, (![D_329]: (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_329))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_329) | ~m1_pre_topc(D_329, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_30, c_537, c_792])).
% 3.65/1.58  tff(c_800, plain, (![D_329]: (k2_partfun1(u1_struct_0('#skF_4'), '#skF_6', '#skF_6', u1_struct_0(D_329))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_329) | ~m1_pre_topc(D_329, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_799])).
% 3.65/1.58  tff(c_866, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_858, c_800])).
% 3.65/1.58  tff(c_873, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_866])).
% 3.65/1.58  tff(c_750, plain, (r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_572])).
% 3.65/1.58  tff(c_878, plain, (r2_funct_2(u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_873, c_750])).
% 3.65/1.58  tff(c_880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_751, c_878])).
% 3.65/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.58  
% 3.65/1.58  Inference rules
% 3.65/1.58  ----------------------
% 3.65/1.58  #Ref     : 0
% 3.65/1.58  #Sup     : 145
% 3.65/1.58  #Fact    : 0
% 3.65/1.58  #Define  : 0
% 3.65/1.58  #Split   : 17
% 3.65/1.58  #Chain   : 0
% 3.65/1.58  #Close   : 0
% 3.65/1.58  
% 3.65/1.58  Ordering : KBO
% 3.65/1.58  
% 3.65/1.58  Simplification rules
% 3.65/1.58  ----------------------
% 3.65/1.58  #Subsume      : 17
% 3.65/1.58  #Demod        : 349
% 3.65/1.58  #Tautology    : 69
% 3.65/1.58  #SimpNegUnit  : 55
% 3.65/1.58  #BackRed      : 32
% 3.65/1.58  
% 3.65/1.58  #Partial instantiations: 0
% 3.65/1.58  #Strategies tried      : 1
% 3.65/1.58  
% 3.65/1.58  Timing (in seconds)
% 3.65/1.58  ----------------------
% 3.65/1.58  Preprocessing        : 0.37
% 3.65/1.58  Parsing              : 0.19
% 3.65/1.58  CNF conversion       : 0.04
% 3.65/1.58  Main loop            : 0.42
% 3.65/1.58  Inferencing          : 0.14
% 3.65/1.58  Reduction            : 0.15
% 3.65/1.58  Demodulation         : 0.11
% 3.65/1.58  BG Simplification    : 0.02
% 3.65/1.58  Subsumption          : 0.08
% 3.65/1.58  Abstraction          : 0.02
% 3.65/1.58  MUC search           : 0.00
% 3.65/1.58  Cooper               : 0.00
% 3.65/1.58  Total                : 0.85
% 3.65/1.58  Index Insertion      : 0.00
% 3.65/1.58  Index Deletion       : 0.00
% 3.65/1.58  Index Matching       : 0.00
% 3.65/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
