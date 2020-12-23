%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:20 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 419 expanded)
%              Number of leaves         :   33 ( 171 expanded)
%              Depth                    :   12
%              Number of atoms          :  362 (3610 expanded)
%              Number of equality atoms :   39 ( 224 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_175,negated_conjecture,(
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

tff(f_86,axiom,(
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

tff(f_118,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
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

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_16,plain,(
    '#skF_1' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_56,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_71,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_56])).

tff(c_79,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_62,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_67,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_62])).

tff(c_80,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_67])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_40])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_65,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_69,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_30])).

tff(c_169,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k2_partfun1(u1_struct_0(A_194),u1_struct_0(B_195),C_196,u1_struct_0(D_197)) = k2_tmap_1(A_194,B_195,C_196,D_197)
      | ~ m1_pre_topc(D_197,A_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_194),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_196,u1_struct_0(A_194),u1_struct_0(B_195))
      | ~ v1_funct_1(C_196)
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_171,plain,(
    ! [D_197] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_197)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_197)
      | ~ m1_pre_topc(D_197,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_169])).

tff(c_176,plain,(
    ! [D_197] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_197)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_197)
      | ~ m1_pre_topc(D_197,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_65,c_46,c_44,c_34,c_69,c_171])).

tff(c_177,plain,(
    ! [D_197] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_197)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_197)
      | ~ m1_pre_topc(D_197,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_48,c_176])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_192,plain,(
    ! [B_200,E_199,D_203,C_202,A_201] :
      ( k3_tmap_1(A_201,B_200,C_202,D_203,E_199) = k2_partfun1(u1_struct_0(C_202),u1_struct_0(B_200),E_199,u1_struct_0(D_203))
      | ~ m1_pre_topc(D_203,C_202)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_202),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_199,u1_struct_0(C_202),u1_struct_0(B_200))
      | ~ v1_funct_1(E_199)
      | ~ m1_pre_topc(D_203,A_201)
      | ~ m1_pre_topc(C_202,A_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_194,plain,(
    ! [A_201,D_203] :
      ( k3_tmap_1(A_201,'#skF_2','#skF_4',D_203,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_203))
      | ~ m1_pre_topc(D_203,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_203,A_201)
      | ~ m1_pre_topc('#skF_4',A_201)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_70,c_192])).

tff(c_199,plain,(
    ! [A_201,D_203] :
      ( k3_tmap_1(A_201,'#skF_2','#skF_4',D_203,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_203))
      | ~ m1_pre_topc(D_203,'#skF_4')
      | ~ m1_pre_topc(D_203,A_201)
      | ~ m1_pre_topc('#skF_4',A_201)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_69,c_194])).

tff(c_220,plain,(
    ! [A_206,D_207] :
      ( k3_tmap_1(A_206,'#skF_2','#skF_4',D_207,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_207))
      | ~ m1_pre_topc(D_207,'#skF_4')
      | ~ m1_pre_topc(D_207,A_206)
      | ~ m1_pre_topc('#skF_4',A_206)
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_199])).

tff(c_224,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_220])).

tff(c_231,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_65,c_68,c_66,c_224])).

tff(c_232,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_231])).

tff(c_259,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_232])).

tff(c_265,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_259])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [D_177,F_178,C_180,A_179,B_181] :
      ( r1_funct_2(A_179,B_181,C_180,D_177,F_178,F_178)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(C_180,D_177)))
      | ~ v1_funct_2(F_178,C_180,D_177)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_181)))
      | ~ v1_funct_2(F_178,A_179,B_181)
      | ~ v1_funct_1(F_178)
      | v1_xboole_0(D_177)
      | v1_xboole_0(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,(
    ! [A_179,B_181] :
      ( r1_funct_2(A_179,B_181,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_179,B_181)))
      | ~ v1_funct_2('#skF_5',A_179,B_181)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_181) ) ),
    inference(resolution,[status(thm)],[c_70,c_81])).

tff(c_90,plain,(
    ! [A_179,B_181] :
      ( r1_funct_2(A_179,B_181,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_179,B_181)))
      | ~ v1_funct_2('#skF_5',A_179,B_181)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_69,c_83])).

tff(c_97,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_103,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_100])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_106])).

tff(c_112,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_22,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_20,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_18,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_14,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_72,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14])).

tff(c_118,plain,(
    ! [E_184,B_189,A_187,C_188,D_185,F_186] :
      ( F_186 = E_184
      | ~ r1_funct_2(A_187,B_189,C_188,D_185,E_184,F_186)
      | ~ m1_subset_1(F_186,k1_zfmisc_1(k2_zfmisc_1(C_188,D_185)))
      | ~ v1_funct_2(F_186,C_188,D_185)
      | ~ v1_funct_1(F_186)
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_187,B_189)))
      | ~ v1_funct_2(E_184,A_187,B_189)
      | ~ v1_funct_1(E_184)
      | v1_xboole_0(D_185)
      | v1_xboole_0(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_118])).

tff(c_130,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_69,c_70,c_22,c_20,c_18,c_122])).

tff(c_131,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_130])).

tff(c_133,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_79])).

tff(c_268,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_133])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_268])).

tff(c_272,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_353,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k2_partfun1(u1_struct_0(A_223),u1_struct_0(B_224),C_225,u1_struct_0(D_226)) = k2_tmap_1(A_223,B_224,C_225,D_226)
      | ~ m1_pre_topc(D_226,A_223)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_223),u1_struct_0(B_224))))
      | ~ v1_funct_2(C_225,u1_struct_0(A_223),u1_struct_0(B_224))
      | ~ v1_funct_1(C_225)
      | ~ l1_pre_topc(B_224)
      | ~ v2_pre_topc(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_355,plain,(
    ! [D_226] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_226)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_226)
      | ~ m1_pre_topc(D_226,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_353])).

tff(c_360,plain,(
    ! [D_226] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_226)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_226)
      | ~ m1_pre_topc(D_226,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_65,c_46,c_44,c_34,c_69,c_355])).

tff(c_361,plain,(
    ! [D_226] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_226)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_226)
      | ~ m1_pre_topc(D_226,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_48,c_360])).

tff(c_375,plain,(
    ! [A_230,E_228,C_231,D_232,B_229] :
      ( k3_tmap_1(A_230,B_229,C_231,D_232,E_228) = k2_partfun1(u1_struct_0(C_231),u1_struct_0(B_229),E_228,u1_struct_0(D_232))
      | ~ m1_pre_topc(D_232,C_231)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_231),u1_struct_0(B_229))))
      | ~ v1_funct_2(E_228,u1_struct_0(C_231),u1_struct_0(B_229))
      | ~ v1_funct_1(E_228)
      | ~ m1_pre_topc(D_232,A_230)
      | ~ m1_pre_topc(C_231,A_230)
      | ~ l1_pre_topc(B_229)
      | ~ v2_pre_topc(B_229)
      | v2_struct_0(B_229)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_377,plain,(
    ! [A_230,D_232] :
      ( k3_tmap_1(A_230,'#skF_2','#skF_4',D_232,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_232))
      | ~ m1_pre_topc(D_232,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_232,A_230)
      | ~ m1_pre_topc('#skF_4',A_230)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_70,c_375])).

tff(c_382,plain,(
    ! [A_230,D_232] :
      ( k3_tmap_1(A_230,'#skF_2','#skF_4',D_232,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_232))
      | ~ m1_pre_topc(D_232,'#skF_4')
      | ~ m1_pre_topc(D_232,A_230)
      | ~ m1_pre_topc('#skF_4',A_230)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_69,c_377])).

tff(c_404,plain,(
    ! [A_235,D_236] :
      ( k3_tmap_1(A_235,'#skF_2','#skF_4',D_236,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_236))
      | ~ m1_pre_topc(D_236,'#skF_4')
      | ~ m1_pre_topc(D_236,A_235)
      | ~ m1_pre_topc('#skF_4',A_235)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_382])).

tff(c_408,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_404])).

tff(c_415,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_65,c_68,c_66,c_408])).

tff(c_416,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_415])).

tff(c_438,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_416])).

tff(c_444,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_438])).

tff(c_276,plain,(
    ! [B_212,C_211,D_208,A_210,F_209] :
      ( r1_funct_2(A_210,B_212,C_211,D_208,F_209,F_209)
      | ~ m1_subset_1(F_209,k1_zfmisc_1(k2_zfmisc_1(C_211,D_208)))
      | ~ v1_funct_2(F_209,C_211,D_208)
      | ~ m1_subset_1(F_209,k1_zfmisc_1(k2_zfmisc_1(A_210,B_212)))
      | ~ v1_funct_2(F_209,A_210,B_212)
      | ~ v1_funct_1(F_209)
      | v1_xboole_0(D_208)
      | v1_xboole_0(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_278,plain,(
    ! [A_210,B_212] :
      ( r1_funct_2(A_210,B_212,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_210,B_212)))
      | ~ v1_funct_2('#skF_5',A_210,B_212)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_212) ) ),
    inference(resolution,[status(thm)],[c_70,c_276])).

tff(c_285,plain,(
    ! [A_210,B_212] :
      ( r1_funct_2(A_210,B_212,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_210,B_212)))
      | ~ v1_funct_2('#skF_5',A_210,B_212)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_69,c_278])).

tff(c_292,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_295,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_298,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_295])).

tff(c_301,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_298])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_301])).

tff(c_307,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_308,plain,(
    ! [C_217,A_216,D_214,E_213,B_218,F_215] :
      ( F_215 = E_213
      | ~ r1_funct_2(A_216,B_218,C_217,D_214,E_213,F_215)
      | ~ m1_subset_1(F_215,k1_zfmisc_1(k2_zfmisc_1(C_217,D_214)))
      | ~ v1_funct_2(F_215,C_217,D_214)
      | ~ v1_funct_1(F_215)
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_216,B_218)))
      | ~ v1_funct_2(E_213,A_216,B_218)
      | ~ v1_funct_1(E_213)
      | v1_xboole_0(D_214)
      | v1_xboole_0(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_310,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_308])).

tff(c_313,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_69,c_70,c_22,c_20,c_18,c_310])).

tff(c_314,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_313])).

tff(c_274,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_67])).

tff(c_315,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_274])).

tff(c_451,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_315])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.43  
% 2.79/1.43  %Foreground sorts:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Background operators:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Foreground operators:
% 2.79/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.79/1.43  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.79/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.79/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.43  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.79/1.43  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.79/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.79/1.43  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.79/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.43  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.79/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.43  
% 2.79/1.45  tff(f_175, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 2.79/1.45  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.79/1.45  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.79/1.45  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.79/1.45  tff(f_59, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.79/1.45  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.79/1.45  tff(c_16, plain, ('#skF_1'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_71, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_56])).
% 2.79/1.45  tff(c_79, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_71])).
% 2.79/1.45  tff(c_62, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_67, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_62])).
% 2.79/1.45  tff(c_80, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_79, c_67])).
% 2.79/1.45  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_40])).
% 2.79/1.45  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 2.79/1.45  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_65, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 2.79/1.45  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_69, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 2.79/1.45  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_30])).
% 2.79/1.45  tff(c_169, plain, (![A_194, B_195, C_196, D_197]: (k2_partfun1(u1_struct_0(A_194), u1_struct_0(B_195), C_196, u1_struct_0(D_197))=k2_tmap_1(A_194, B_195, C_196, D_197) | ~m1_pre_topc(D_197, A_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_194), u1_struct_0(B_195)))) | ~v1_funct_2(C_196, u1_struct_0(A_194), u1_struct_0(B_195)) | ~v1_funct_1(C_196) | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.79/1.45  tff(c_171, plain, (![D_197]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_197))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_197) | ~m1_pre_topc(D_197, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_169])).
% 2.79/1.45  tff(c_176, plain, (![D_197]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_197))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_197) | ~m1_pre_topc(D_197, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_65, c_46, c_44, c_34, c_69, c_171])).
% 2.79/1.45  tff(c_177, plain, (![D_197]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_197))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_197) | ~m1_pre_topc(D_197, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_48, c_176])).
% 2.79/1.45  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 2.79/1.45  tff(c_192, plain, (![B_200, E_199, D_203, C_202, A_201]: (k3_tmap_1(A_201, B_200, C_202, D_203, E_199)=k2_partfun1(u1_struct_0(C_202), u1_struct_0(B_200), E_199, u1_struct_0(D_203)) | ~m1_pre_topc(D_203, C_202) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_202), u1_struct_0(B_200)))) | ~v1_funct_2(E_199, u1_struct_0(C_202), u1_struct_0(B_200)) | ~v1_funct_1(E_199) | ~m1_pre_topc(D_203, A_201) | ~m1_pre_topc(C_202, A_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.79/1.45  tff(c_194, plain, (![A_201, D_203]: (k3_tmap_1(A_201, '#skF_2', '#skF_4', D_203, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_203)) | ~m1_pre_topc(D_203, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_203, A_201) | ~m1_pre_topc('#skF_4', A_201) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(resolution, [status(thm)], [c_70, c_192])).
% 2.79/1.45  tff(c_199, plain, (![A_201, D_203]: (k3_tmap_1(A_201, '#skF_2', '#skF_4', D_203, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_203)) | ~m1_pre_topc(D_203, '#skF_4') | ~m1_pre_topc(D_203, A_201) | ~m1_pre_topc('#skF_4', A_201) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_69, c_194])).
% 2.79/1.45  tff(c_220, plain, (![A_206, D_207]: (k3_tmap_1(A_206, '#skF_2', '#skF_4', D_207, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_207)) | ~m1_pre_topc(D_207, '#skF_4') | ~m1_pre_topc(D_207, A_206) | ~m1_pre_topc('#skF_4', A_206) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(negUnitSimplification, [status(thm)], [c_48, c_199])).
% 2.79/1.45  tff(c_224, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_220])).
% 2.79/1.45  tff(c_231, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_65, c_68, c_66, c_224])).
% 2.79/1.45  tff(c_232, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_231])).
% 2.79/1.45  tff(c_259, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_177, c_232])).
% 2.79/1.45  tff(c_265, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_259])).
% 2.79/1.45  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.45  tff(c_81, plain, (![D_177, F_178, C_180, A_179, B_181]: (r1_funct_2(A_179, B_181, C_180, D_177, F_178, F_178) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(C_180, D_177))) | ~v1_funct_2(F_178, C_180, D_177) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_181))) | ~v1_funct_2(F_178, A_179, B_181) | ~v1_funct_1(F_178) | v1_xboole_0(D_177) | v1_xboole_0(B_181))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_83, plain, (![A_179, B_181]: (r1_funct_2(A_179, B_181, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_179, B_181))) | ~v1_funct_2('#skF_5', A_179, B_181) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_181))), inference(resolution, [status(thm)], [c_70, c_81])).
% 2.79/1.45  tff(c_90, plain, (![A_179, B_181]: (r1_funct_2(A_179, B_181, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_179, B_181))) | ~v1_funct_2('#skF_5', A_179, B_181) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_181))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_69, c_83])).
% 2.79/1.45  tff(c_97, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.79/1.45  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.45  tff(c_100, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_97, c_4])).
% 2.79/1.45  tff(c_103, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_100])).
% 2.79/1.45  tff(c_106, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_103])).
% 2.79/1.45  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_106])).
% 2.79/1.45  tff(c_112, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_90])).
% 2.79/1.45  tff(c_22, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_20, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_18, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_14, plain, (r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_175])).
% 2.79/1.45  tff(c_72, plain, (r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14])).
% 2.79/1.45  tff(c_118, plain, (![E_184, B_189, A_187, C_188, D_185, F_186]: (F_186=E_184 | ~r1_funct_2(A_187, B_189, C_188, D_185, E_184, F_186) | ~m1_subset_1(F_186, k1_zfmisc_1(k2_zfmisc_1(C_188, D_185))) | ~v1_funct_2(F_186, C_188, D_185) | ~v1_funct_1(F_186) | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_187, B_189))) | ~v1_funct_2(E_184, A_187, B_189) | ~v1_funct_1(E_184) | v1_xboole_0(D_185) | v1_xboole_0(B_189))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_122, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_118])).
% 2.79/1.45  tff(c_130, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_69, c_70, c_22, c_20, c_18, c_122])).
% 2.79/1.45  tff(c_131, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_112, c_130])).
% 2.79/1.45  tff(c_133, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_79])).
% 2.79/1.45  tff(c_268, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_133])).
% 2.79/1.45  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_268])).
% 2.79/1.45  tff(c_272, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_71])).
% 2.79/1.45  tff(c_353, plain, (![A_223, B_224, C_225, D_226]: (k2_partfun1(u1_struct_0(A_223), u1_struct_0(B_224), C_225, u1_struct_0(D_226))=k2_tmap_1(A_223, B_224, C_225, D_226) | ~m1_pre_topc(D_226, A_223) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_223), u1_struct_0(B_224)))) | ~v1_funct_2(C_225, u1_struct_0(A_223), u1_struct_0(B_224)) | ~v1_funct_1(C_225) | ~l1_pre_topc(B_224) | ~v2_pre_topc(B_224) | v2_struct_0(B_224) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.79/1.45  tff(c_355, plain, (![D_226]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_226))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_226) | ~m1_pre_topc(D_226, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_353])).
% 2.79/1.45  tff(c_360, plain, (![D_226]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_226))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_226) | ~m1_pre_topc(D_226, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_65, c_46, c_44, c_34, c_69, c_355])).
% 2.79/1.45  tff(c_361, plain, (![D_226]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_226))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_226) | ~m1_pre_topc(D_226, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_48, c_360])).
% 2.79/1.45  tff(c_375, plain, (![A_230, E_228, C_231, D_232, B_229]: (k3_tmap_1(A_230, B_229, C_231, D_232, E_228)=k2_partfun1(u1_struct_0(C_231), u1_struct_0(B_229), E_228, u1_struct_0(D_232)) | ~m1_pre_topc(D_232, C_231) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_231), u1_struct_0(B_229)))) | ~v1_funct_2(E_228, u1_struct_0(C_231), u1_struct_0(B_229)) | ~v1_funct_1(E_228) | ~m1_pre_topc(D_232, A_230) | ~m1_pre_topc(C_231, A_230) | ~l1_pre_topc(B_229) | ~v2_pre_topc(B_229) | v2_struct_0(B_229) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.79/1.45  tff(c_377, plain, (![A_230, D_232]: (k3_tmap_1(A_230, '#skF_2', '#skF_4', D_232, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_232)) | ~m1_pre_topc(D_232, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_232, A_230) | ~m1_pre_topc('#skF_4', A_230) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_70, c_375])).
% 2.79/1.45  tff(c_382, plain, (![A_230, D_232]: (k3_tmap_1(A_230, '#skF_2', '#skF_4', D_232, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_232)) | ~m1_pre_topc(D_232, '#skF_4') | ~m1_pre_topc(D_232, A_230) | ~m1_pre_topc('#skF_4', A_230) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_69, c_377])).
% 2.79/1.45  tff(c_404, plain, (![A_235, D_236]: (k3_tmap_1(A_235, '#skF_2', '#skF_4', D_236, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_236)) | ~m1_pre_topc(D_236, '#skF_4') | ~m1_pre_topc(D_236, A_235) | ~m1_pre_topc('#skF_4', A_235) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(negUnitSimplification, [status(thm)], [c_48, c_382])).
% 2.79/1.45  tff(c_408, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_404])).
% 2.79/1.45  tff(c_415, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_65, c_68, c_66, c_408])).
% 2.79/1.45  tff(c_416, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_415])).
% 2.79/1.45  tff(c_438, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_361, c_416])).
% 2.79/1.45  tff(c_444, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_438])).
% 2.79/1.45  tff(c_276, plain, (![B_212, C_211, D_208, A_210, F_209]: (r1_funct_2(A_210, B_212, C_211, D_208, F_209, F_209) | ~m1_subset_1(F_209, k1_zfmisc_1(k2_zfmisc_1(C_211, D_208))) | ~v1_funct_2(F_209, C_211, D_208) | ~m1_subset_1(F_209, k1_zfmisc_1(k2_zfmisc_1(A_210, B_212))) | ~v1_funct_2(F_209, A_210, B_212) | ~v1_funct_1(F_209) | v1_xboole_0(D_208) | v1_xboole_0(B_212))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_278, plain, (![A_210, B_212]: (r1_funct_2(A_210, B_212, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_210, B_212))) | ~v1_funct_2('#skF_5', A_210, B_212) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_212))), inference(resolution, [status(thm)], [c_70, c_276])).
% 2.79/1.45  tff(c_285, plain, (![A_210, B_212]: (r1_funct_2(A_210, B_212, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_210, B_212))) | ~v1_funct_2('#skF_5', A_210, B_212) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_69, c_278])).
% 2.79/1.45  tff(c_292, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_285])).
% 2.79/1.45  tff(c_295, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_292, c_4])).
% 2.79/1.45  tff(c_298, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_295])).
% 2.79/1.45  tff(c_301, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_298])).
% 2.79/1.45  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_301])).
% 2.79/1.45  tff(c_307, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_285])).
% 2.79/1.45  tff(c_308, plain, (![C_217, A_216, D_214, E_213, B_218, F_215]: (F_215=E_213 | ~r1_funct_2(A_216, B_218, C_217, D_214, E_213, F_215) | ~m1_subset_1(F_215, k1_zfmisc_1(k2_zfmisc_1(C_217, D_214))) | ~v1_funct_2(F_215, C_217, D_214) | ~v1_funct_1(F_215) | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_216, B_218))) | ~v1_funct_2(E_213, A_216, B_218) | ~v1_funct_1(E_213) | v1_xboole_0(D_214) | v1_xboole_0(B_218))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_310, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_308])).
% 2.79/1.45  tff(c_313, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_69, c_70, c_22, c_20, c_18, c_310])).
% 2.79/1.45  tff(c_314, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_307, c_313])).
% 2.79/1.45  tff(c_274, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_272, c_67])).
% 2.79/1.45  tff(c_315, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_274])).
% 2.79/1.45  tff(c_451, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_315])).
% 2.79/1.45  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_451])).
% 2.79/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  Inference rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Ref     : 0
% 2.79/1.45  #Sup     : 65
% 2.79/1.45  #Fact    : 0
% 2.79/1.45  #Define  : 0
% 2.79/1.45  #Split   : 10
% 2.79/1.45  #Chain   : 0
% 2.79/1.45  #Close   : 0
% 2.79/1.45  
% 2.79/1.45  Ordering : KBO
% 2.79/1.45  
% 2.79/1.45  Simplification rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Subsume      : 4
% 2.79/1.45  #Demod        : 162
% 2.79/1.45  #Tautology    : 39
% 2.79/1.45  #SimpNegUnit  : 34
% 2.79/1.45  #BackRed      : 17
% 2.79/1.45  
% 2.79/1.45  #Partial instantiations: 0
% 2.79/1.45  #Strategies tried      : 1
% 2.79/1.45  
% 2.79/1.45  Timing (in seconds)
% 2.79/1.45  ----------------------
% 2.79/1.45  Preprocessing        : 0.36
% 2.79/1.45  Parsing              : 0.18
% 2.79/1.45  CNF conversion       : 0.05
% 2.79/1.45  Main loop            : 0.29
% 2.79/1.45  Inferencing          : 0.09
% 2.79/1.45  Reduction            : 0.11
% 2.79/1.46  Demodulation         : 0.08
% 2.79/1.46  BG Simplification    : 0.02
% 2.79/1.46  Subsumption          : 0.04
% 2.79/1.46  Abstraction          : 0.01
% 2.79/1.46  MUC search           : 0.00
% 2.79/1.46  Cooper               : 0.00
% 2.79/1.46  Total                : 0.69
% 2.79/1.46  Index Insertion      : 0.00
% 2.79/1.46  Index Deletion       : 0.00
% 2.79/1.46  Index Matching       : 0.00
% 2.79/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
