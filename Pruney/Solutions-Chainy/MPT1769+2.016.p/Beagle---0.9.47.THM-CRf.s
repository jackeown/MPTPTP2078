%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:20 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  169 (1348 expanded)
%              Number of leaves         :   37 ( 493 expanded)
%              Depth                    :   17
%              Number of atoms          :  563 (8075 expanded)
%              Number of equality atoms :   66 ( 790 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_96,axiom,(
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

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_181] :
      ( u1_struct_0(A_181) = k2_struct_0(A_181)
      | ~ l1_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_182] :
      ( u1_struct_0(A_182) = k2_struct_0(A_182)
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_95,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_20,plain,(
    '#skF_1' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_71,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_66])).

tff(c_159,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_71])).

tff(c_160,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_44])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_69,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_54])).

tff(c_94,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_87])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_73,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_98,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_73])).

tff(c_109,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_98])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_111,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_74])).

tff(c_114,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k2_partfun1(A_184,B_185,C_186,D_187) = k7_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [D_187] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',D_187) = k7_relat_1('#skF_5',D_187)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_111,c_114])).

tff(c_129,plain,(
    ! [D_187] : k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',D_187) = k7_relat_1('#skF_5',D_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_120])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_248,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( k2_partfun1(u1_struct_0(A_208),u1_struct_0(B_209),C_210,u1_struct_0(D_211)) = k2_tmap_1(A_208,B_209,C_210,D_211)
      | ~ m1_pre_topc(D_211,A_208)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_208),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,u1_struct_0(A_208),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_250,plain,(
    ! [B_209,C_210,D_211] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_209),C_210,u1_struct_0(D_211)) = k2_tmap_1('#skF_4',B_209,C_210,D_211)
      | ~ m1_pre_topc(D_211,'#skF_4')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,u1_struct_0('#skF_4'),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_248])).

tff(c_258,plain,(
    ! [B_209,C_210,D_211] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_209),C_210,u1_struct_0(D_211)) = k2_tmap_1('#skF_4',B_209,C_210,D_211)
      | ~ m1_pre_topc(D_211,'#skF_4')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,k2_struct_0('#skF_4'),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_94,c_94,c_250])).

tff(c_269,plain,(
    ! [B_212,C_213,D_214] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_212),C_213,u1_struct_0(D_214)) = k2_tmap_1('#skF_4',B_212,C_213,D_214)
      | ~ m1_pre_topc(D_214,'#skF_4')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_212))))
      | ~ v1_funct_2(C_213,k2_struct_0('#skF_4'),u1_struct_0(B_212))
      | ~ v1_funct_1(C_213)
      | ~ l1_pre_topc(B_212)
      | ~ v2_pre_topc(B_212)
      | v2_struct_0(B_212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_258])).

tff(c_273,plain,(
    ! [C_213,D_214] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_213,u1_struct_0(D_214)) = k2_tmap_1('#skF_4','#skF_2',C_213,D_214)
      | ~ m1_pre_topc(D_214,'#skF_4')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_213,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_213)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_269])).

tff(c_278,plain,(
    ! [C_213,D_214] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_213,u1_struct_0(D_214)) = k2_tmap_1('#skF_4','#skF_2',C_213,D_214)
      | ~ m1_pre_topc(D_214,'#skF_4')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_213,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_213)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_95,c_95,c_273])).

tff(c_281,plain,(
    ! [C_217,D_218] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_217,u1_struct_0(D_218)) = k2_tmap_1('#skF_4','#skF_2',C_217,D_218)
      | ~ m1_pre_topc(D_218,'#skF_4')
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_217,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_278])).

tff(c_283,plain,(
    ! [D_218] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_218)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_218)
      | ~ m1_pre_topc(D_218,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_111,c_281])).

tff(c_286,plain,(
    ! [D_218] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_218)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_218)
      | ~ m1_pre_topc(D_218,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109,c_129,c_283])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_72,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_40])).

tff(c_287,plain,(
    ! [B_221,E_223,A_220,D_222,C_219] :
      ( k3_tmap_1(A_220,B_221,C_219,D_222,E_223) = k2_partfun1(u1_struct_0(C_219),u1_struct_0(B_221),E_223,u1_struct_0(D_222))
      | ~ m1_pre_topc(D_222,C_219)
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_219),u1_struct_0(B_221))))
      | ~ v1_funct_2(E_223,u1_struct_0(C_219),u1_struct_0(B_221))
      | ~ v1_funct_1(E_223)
      | ~ m1_pre_topc(D_222,A_220)
      | ~ m1_pre_topc(C_219,A_220)
      | ~ l1_pre_topc(B_221)
      | ~ v2_pre_topc(B_221)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_289,plain,(
    ! [A_220,B_221,D_222,E_223] :
      ( k3_tmap_1(A_220,B_221,'#skF_4',D_222,E_223) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_221),E_223,u1_struct_0(D_222))
      | ~ m1_pre_topc(D_222,'#skF_4')
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_221))))
      | ~ v1_funct_2(E_223,u1_struct_0('#skF_4'),u1_struct_0(B_221))
      | ~ v1_funct_1(E_223)
      | ~ m1_pre_topc(D_222,A_220)
      | ~ m1_pre_topc('#skF_4',A_220)
      | ~ l1_pre_topc(B_221)
      | ~ v2_pre_topc(B_221)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_287])).

tff(c_402,plain,(
    ! [A_248,B_249,D_250,E_251] :
      ( k3_tmap_1(A_248,B_249,'#skF_4',D_250,E_251) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_249),E_251,u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,'#skF_4')
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_249))))
      | ~ v1_funct_2(E_251,k2_struct_0('#skF_4'),u1_struct_0(B_249))
      | ~ v1_funct_1(E_251)
      | ~ m1_pre_topc(D_250,A_248)
      | ~ m1_pre_topc('#skF_4',A_248)
      | ~ l1_pre_topc(B_249)
      | ~ v2_pre_topc(B_249)
      | v2_struct_0(B_249)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_289])).

tff(c_406,plain,(
    ! [A_248,D_250,E_251] :
      ( k3_tmap_1(A_248,'#skF_2','#skF_4',D_250,E_251) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_251,u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,'#skF_4')
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_251,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_251)
      | ~ m1_pre_topc(D_250,A_248)
      | ~ m1_pre_topc('#skF_4',A_248)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_402])).

tff(c_411,plain,(
    ! [A_248,D_250,E_251] :
      ( k3_tmap_1(A_248,'#skF_2','#skF_4',D_250,E_251) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_251,u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,'#skF_4')
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_251,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_251)
      | ~ m1_pre_topc(D_250,A_248)
      | ~ m1_pre_topc('#skF_4',A_248)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_95,c_95,c_406])).

tff(c_414,plain,(
    ! [A_255,D_256,E_257] :
      ( k3_tmap_1(A_255,'#skF_2','#skF_4',D_256,E_257) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_257,u1_struct_0(D_256))
      | ~ m1_pre_topc(D_256,'#skF_4')
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_257,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_257)
      | ~ m1_pre_topc(D_256,A_255)
      | ~ m1_pre_topc('#skF_4',A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_411])).

tff(c_416,plain,(
    ! [A_255,D_256] :
      ( k3_tmap_1(A_255,'#skF_2','#skF_4',D_256,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_256))
      | ~ m1_pre_topc(D_256,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_256,A_255)
      | ~ m1_pre_topc('#skF_4',A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_111,c_414])).

tff(c_420,plain,(
    ! [D_258,A_259] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_258)) = k3_tmap_1(A_259,'#skF_2','#skF_4',D_258,'#skF_5')
      | ~ m1_pre_topc(D_258,'#skF_4')
      | ~ m1_pre_topc(D_258,A_259)
      | ~ m1_pre_topc('#skF_4',A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109,c_129,c_416])).

tff(c_422,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_420])).

tff(c_427,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_72,c_70,c_422])).

tff(c_428,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_427])).

tff(c_440,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_428])).

tff(c_446,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_440])).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_30,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_99,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_30])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_96,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_28])).

tff(c_161,plain,(
    ! [D_195,C_194,A_192,F_191,B_193] :
      ( r1_funct_2(A_192,B_193,C_194,D_195,F_191,F_191)
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(C_194,D_195)))
      | ~ v1_funct_2(F_191,C_194,D_195)
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2(F_191,A_192,B_193)
      | ~ v1_funct_1(F_191)
      | v1_xboole_0(D_195)
      | v1_xboole_0(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_163,plain,(
    ! [A_192,B_193] :
      ( r1_funct_2(A_192,B_193,u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),k2_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2('#skF_6',A_192,B_193)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | v1_xboole_0(B_193) ) ),
    inference(resolution,[status(thm)],[c_96,c_161])).

tff(c_170,plain,(
    ! [A_192,B_193] :
      ( r1_funct_2(A_192,B_193,u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2('#skF_6',A_192,B_193)
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | v1_xboole_0(B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99,c_163])).

tff(c_177,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_180,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_8])).

tff(c_183,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_180])).

tff(c_186,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_186])).

tff(c_192,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_26,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_24,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_97,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_24])).

tff(c_108,plain,(
    v1_funct_2('#skF_7',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_97])).

tff(c_22,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_112,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_22])).

tff(c_18,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_76,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_113,plain,(
    r1_funct_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_95,c_95,c_76])).

tff(c_196,plain,(
    ! [D_205,C_204,B_203,E_202,A_201,F_200] :
      ( F_200 = E_202
      | ~ r1_funct_2(A_201,B_203,C_204,D_205,E_202,F_200)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_204,D_205)))
      | ~ v1_funct_2(F_200,C_204,D_205)
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_201,B_203)))
      | ~ v1_funct_2(E_202,A_201,B_203)
      | ~ v1_funct_1(E_202)
      | v1_xboole_0(D_205)
      | v1_xboole_0(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_202,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_113,c_196])).

tff(c_215,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109,c_111,c_26,c_108,c_112,c_202])).

tff(c_216,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_215])).

tff(c_60,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_75,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_60])).

tff(c_157,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_75])).

tff(c_158,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_218,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_158])).

tff(c_452,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_218])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_452])).

tff(c_456,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_158])).

tff(c_460,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_561,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k2_partfun1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,u1_struct_0(D_286)) = k2_tmap_1(A_283,B_284,C_285,D_286)
      | ~ m1_pre_topc(D_286,A_283)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,u1_struct_0(A_283),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_563,plain,(
    ! [B_284,C_285,D_286] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_284),C_285,u1_struct_0(D_286)) = k2_tmap_1('#skF_4',B_284,C_285,D_286)
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,u1_struct_0('#skF_4'),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_561])).

tff(c_571,plain,(
    ! [B_284,C_285,D_286] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_284),C_285,u1_struct_0(D_286)) = k2_tmap_1('#skF_4',B_284,C_285,D_286)
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,k2_struct_0('#skF_4'),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | v2_struct_0(B_284)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_94,c_94,c_563])).

tff(c_582,plain,(
    ! [B_287,C_288,D_289] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_287),C_288,u1_struct_0(D_289)) = k2_tmap_1('#skF_4',B_287,C_288,D_289)
      | ~ m1_pre_topc(D_289,'#skF_4')
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_287))))
      | ~ v1_funct_2(C_288,k2_struct_0('#skF_4'),u1_struct_0(B_287))
      | ~ v1_funct_1(C_288)
      | ~ l1_pre_topc(B_287)
      | ~ v2_pre_topc(B_287)
      | v2_struct_0(B_287) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_571])).

tff(c_586,plain,(
    ! [C_288,D_289] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_288,u1_struct_0(D_289)) = k2_tmap_1('#skF_4','#skF_2',C_288,D_289)
      | ~ m1_pre_topc(D_289,'#skF_4')
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_288,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_288)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_582])).

tff(c_591,plain,(
    ! [C_288,D_289] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_288,u1_struct_0(D_289)) = k2_tmap_1('#skF_4','#skF_2',C_288,D_289)
      | ~ m1_pre_topc(D_289,'#skF_4')
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_288,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_288)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_95,c_95,c_586])).

tff(c_594,plain,(
    ! [C_292,D_293] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_292,u1_struct_0(D_293)) = k2_tmap_1('#skF_4','#skF_2',C_292,D_293)
      | ~ m1_pre_topc(D_293,'#skF_4')
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_292,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_292) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_591])).

tff(c_596,plain,(
    ! [D_293] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_293)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_293)
      | ~ m1_pre_topc(D_293,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_111,c_594])).

tff(c_599,plain,(
    ! [D_293] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_293)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_293)
      | ~ m1_pre_topc(D_293,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109,c_129,c_596])).

tff(c_640,plain,(
    ! [D_301,E_302,A_299,B_300,C_298] :
      ( k3_tmap_1(A_299,B_300,C_298,D_301,E_302) = k2_partfun1(u1_struct_0(C_298),u1_struct_0(B_300),E_302,u1_struct_0(D_301))
      | ~ m1_pre_topc(D_301,C_298)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298),u1_struct_0(B_300))))
      | ~ v1_funct_2(E_302,u1_struct_0(C_298),u1_struct_0(B_300))
      | ~ v1_funct_1(E_302)
      | ~ m1_pre_topc(D_301,A_299)
      | ~ m1_pre_topc(C_298,A_299)
      | ~ l1_pre_topc(B_300)
      | ~ v2_pre_topc(B_300)
      | v2_struct_0(B_300)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_648,plain,(
    ! [A_299,C_298,D_301,E_302] :
      ( k3_tmap_1(A_299,'#skF_2',C_298,D_301,E_302) = k2_partfun1(u1_struct_0(C_298),u1_struct_0('#skF_2'),E_302,u1_struct_0(D_301))
      | ~ m1_pre_topc(D_301,C_298)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_302,u1_struct_0(C_298),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_302)
      | ~ m1_pre_topc(D_301,A_299)
      | ~ m1_pre_topc(C_298,A_299)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_640])).

tff(c_655,plain,(
    ! [A_299,C_298,D_301,E_302] :
      ( k3_tmap_1(A_299,'#skF_2',C_298,D_301,E_302) = k2_partfun1(u1_struct_0(C_298),k2_struct_0('#skF_2'),E_302,u1_struct_0(D_301))
      | ~ m1_pre_topc(D_301,C_298)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_302,u1_struct_0(C_298),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_302)
      | ~ m1_pre_topc(D_301,A_299)
      | ~ m1_pre_topc(C_298,A_299)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_95,c_95,c_648])).

tff(c_681,plain,(
    ! [A_313,C_314,D_315,E_316] :
      ( k3_tmap_1(A_313,'#skF_2',C_314,D_315,E_316) = k2_partfun1(u1_struct_0(C_314),k2_struct_0('#skF_2'),E_316,u1_struct_0(D_315))
      | ~ m1_pre_topc(D_315,C_314)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_316,u1_struct_0(C_314),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_316)
      | ~ m1_pre_topc(D_315,A_313)
      | ~ m1_pre_topc(C_314,A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_655])).

tff(c_685,plain,(
    ! [A_313,D_315,E_316] :
      ( k3_tmap_1(A_313,'#skF_2','#skF_4',D_315,E_316) = k2_partfun1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_316,u1_struct_0(D_315))
      | ~ m1_pre_topc(D_315,'#skF_4')
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_316,u1_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_316)
      | ~ m1_pre_topc(D_315,A_313)
      | ~ m1_pre_topc('#skF_4',A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_681])).

tff(c_718,plain,(
    ! [A_332,D_333,E_334] :
      ( k3_tmap_1(A_332,'#skF_2','#skF_4',D_333,E_334) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_334,u1_struct_0(D_333))
      | ~ m1_pre_topc(D_333,'#skF_4')
      | ~ m1_subset_1(E_334,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_334,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_334)
      | ~ m1_pre_topc(D_333,A_332)
      | ~ m1_pre_topc('#skF_4',A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_685])).

tff(c_720,plain,(
    ! [A_332,D_333] :
      ( k3_tmap_1(A_332,'#skF_2','#skF_4',D_333,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_333))
      | ~ m1_pre_topc(D_333,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_333,A_332)
      | ~ m1_pre_topc('#skF_4',A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(resolution,[status(thm)],[c_111,c_718])).

tff(c_724,plain,(
    ! [D_335,A_336] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_335)) = k3_tmap_1(A_336,'#skF_2','#skF_4',D_335,'#skF_5')
      | ~ m1_pre_topc(D_335,'#skF_4')
      | ~ m1_pre_topc(D_335,A_336)
      | ~ m1_pre_topc('#skF_4',A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109,c_129,c_720])).

tff(c_726,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_724])).

tff(c_731,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_72,c_70,c_726])).

tff(c_732,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_731])).

tff(c_744,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_732])).

tff(c_750,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_744])).

tff(c_468,plain,(
    ! [F_260,D_264,C_263,B_262,A_261] :
      ( r1_funct_2(A_261,B_262,C_263,D_264,F_260,F_260)
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1(C_263,D_264)))
      | ~ v1_funct_2(F_260,C_263,D_264)
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2(F_260,A_261,B_262)
      | ~ v1_funct_1(F_260)
      | v1_xboole_0(D_264)
      | v1_xboole_0(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_470,plain,(
    ! [A_261,B_262] :
      ( r1_funct_2(A_261,B_262,u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),k2_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2('#skF_6',A_261,B_262)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | v1_xboole_0(B_262) ) ),
    inference(resolution,[status(thm)],[c_96,c_468])).

tff(c_477,plain,(
    ! [A_261,B_262] :
      ( r1_funct_2(A_261,B_262,u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2('#skF_6',A_261,B_262)
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | v1_xboole_0(B_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99,c_470])).

tff(c_484,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_487,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_484,c_8])).

tff(c_490,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_487])).

tff(c_499,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_490])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_499])).

tff(c_505,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_511,plain,(
    ! [F_277,A_278,B_280,C_281,D_282,E_279] :
      ( F_277 = E_279
      | ~ r1_funct_2(A_278,B_280,C_281,D_282,E_279,F_277)
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(C_281,D_282)))
      | ~ v1_funct_2(F_277,C_281,D_282)
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_278,B_280)))
      | ~ v1_funct_2(E_279,A_278,B_280)
      | ~ v1_funct_1(E_279)
      | v1_xboole_0(D_282)
      | v1_xboole_0(B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_519,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_113,c_511])).

tff(c_537,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109,c_111,c_26,c_108,c_112,c_519])).

tff(c_538,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_537])).

tff(c_461,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_540,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_461])).

tff(c_767,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_540])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:25 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.59  
% 3.49/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.60  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.49/1.60  
% 3.49/1.60  %Foreground sorts:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Background operators:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Foreground operators:
% 3.49/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.49/1.60  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.49/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.49/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.60  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.49/1.60  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.49/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.49/1.60  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.49/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.49/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.60  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.49/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.60  
% 3.49/1.62  tff(f_185, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 3.49/1.62  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.49/1.62  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.49/1.62  tff(f_31, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.49/1.62  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.49/1.62  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.49/1.62  tff(f_69, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.49/1.62  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.49/1.62  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_6, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.62  tff(c_82, plain, (![A_181]: (u1_struct_0(A_181)=k2_struct_0(A_181) | ~l1_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.62  tff(c_87, plain, (![A_182]: (u1_struct_0(A_182)=k2_struct_0(A_182) | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_6, c_82])).
% 3.49/1.62  tff(c_95, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_87])).
% 3.49/1.62  tff(c_20, plain, ('#skF_1'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_66, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_71, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_66])).
% 3.49/1.62  tff(c_159, plain, (r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_95, c_71])).
% 3.49/1.62  tff(c_160, plain, (r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_159])).
% 3.49/1.62  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_44])).
% 3.49/1.62  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_69, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_54])).
% 3.49/1.62  tff(c_94, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_69, c_87])).
% 3.49/1.62  tff(c_36, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_73, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_36])).
% 3.49/1.62  tff(c_98, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_73])).
% 3.49/1.62  tff(c_109, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_98])).
% 3.49/1.62  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34])).
% 3.49/1.62  tff(c_111, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_74])).
% 3.49/1.62  tff(c_114, plain, (![A_184, B_185, C_186, D_187]: (k2_partfun1(A_184, B_185, C_186, D_187)=k7_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.62  tff(c_120, plain, (![D_187]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', D_187)=k7_relat_1('#skF_5', D_187) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_111, c_114])).
% 3.49/1.62  tff(c_129, plain, (![D_187]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', D_187)=k7_relat_1('#skF_5', D_187))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_120])).
% 3.49/1.62  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56])).
% 3.49/1.62  tff(c_248, plain, (![A_208, B_209, C_210, D_211]: (k2_partfun1(u1_struct_0(A_208), u1_struct_0(B_209), C_210, u1_struct_0(D_211))=k2_tmap_1(A_208, B_209, C_210, D_211) | ~m1_pre_topc(D_211, A_208) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_208), u1_struct_0(B_209)))) | ~v1_funct_2(C_210, u1_struct_0(A_208), u1_struct_0(B_209)) | ~v1_funct_1(C_210) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.49/1.62  tff(c_250, plain, (![B_209, C_210, D_211]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_209), C_210, u1_struct_0(D_211))=k2_tmap_1('#skF_4', B_209, C_210, D_211) | ~m1_pre_topc(D_211, '#skF_4') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_209)))) | ~v1_funct_2(C_210, u1_struct_0('#skF_4'), u1_struct_0(B_209)) | ~v1_funct_1(C_210) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_248])).
% 3.49/1.62  tff(c_258, plain, (![B_209, C_210, D_211]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_209), C_210, u1_struct_0(D_211))=k2_tmap_1('#skF_4', B_209, C_210, D_211) | ~m1_pre_topc(D_211, '#skF_4') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_209)))) | ~v1_funct_2(C_210, k2_struct_0('#skF_4'), u1_struct_0(B_209)) | ~v1_funct_1(C_210) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_94, c_94, c_250])).
% 3.49/1.62  tff(c_269, plain, (![B_212, C_213, D_214]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_212), C_213, u1_struct_0(D_214))=k2_tmap_1('#skF_4', B_212, C_213, D_214) | ~m1_pre_topc(D_214, '#skF_4') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_212)))) | ~v1_funct_2(C_213, k2_struct_0('#skF_4'), u1_struct_0(B_212)) | ~v1_funct_1(C_213) | ~l1_pre_topc(B_212) | ~v2_pre_topc(B_212) | v2_struct_0(B_212))), inference(negUnitSimplification, [status(thm)], [c_42, c_258])).
% 3.49/1.62  tff(c_273, plain, (![C_213, D_214]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_213, u1_struct_0(D_214))=k2_tmap_1('#skF_4', '#skF_2', C_213, D_214) | ~m1_pre_topc(D_214, '#skF_4') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_213, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_213) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_269])).
% 3.49/1.62  tff(c_278, plain, (![C_213, D_214]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_213, u1_struct_0(D_214))=k2_tmap_1('#skF_4', '#skF_2', C_213, D_214) | ~m1_pre_topc(D_214, '#skF_4') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_213, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_213) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_95, c_95, c_273])).
% 3.49/1.62  tff(c_281, plain, (![C_217, D_218]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_217, u1_struct_0(D_218))=k2_tmap_1('#skF_4', '#skF_2', C_217, D_218) | ~m1_pre_topc(D_218, '#skF_4') | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_217, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_217))), inference(negUnitSimplification, [status(thm)], [c_52, c_278])).
% 3.49/1.62  tff(c_283, plain, (![D_218]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_218))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_218) | ~m1_pre_topc(D_218, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_111, c_281])).
% 3.49/1.62  tff(c_286, plain, (![D_218]: (k7_relat_1('#skF_5', u1_struct_0(D_218))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_218) | ~m1_pre_topc(D_218, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109, c_129, c_283])).
% 3.49/1.62  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_72, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_40])).
% 3.49/1.62  tff(c_287, plain, (![B_221, E_223, A_220, D_222, C_219]: (k3_tmap_1(A_220, B_221, C_219, D_222, E_223)=k2_partfun1(u1_struct_0(C_219), u1_struct_0(B_221), E_223, u1_struct_0(D_222)) | ~m1_pre_topc(D_222, C_219) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_219), u1_struct_0(B_221)))) | ~v1_funct_2(E_223, u1_struct_0(C_219), u1_struct_0(B_221)) | ~v1_funct_1(E_223) | ~m1_pre_topc(D_222, A_220) | ~m1_pre_topc(C_219, A_220) | ~l1_pre_topc(B_221) | ~v2_pre_topc(B_221) | v2_struct_0(B_221) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.49/1.62  tff(c_289, plain, (![A_220, B_221, D_222, E_223]: (k3_tmap_1(A_220, B_221, '#skF_4', D_222, E_223)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_221), E_223, u1_struct_0(D_222)) | ~m1_pre_topc(D_222, '#skF_4') | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_221)))) | ~v1_funct_2(E_223, u1_struct_0('#skF_4'), u1_struct_0(B_221)) | ~v1_funct_1(E_223) | ~m1_pre_topc(D_222, A_220) | ~m1_pre_topc('#skF_4', A_220) | ~l1_pre_topc(B_221) | ~v2_pre_topc(B_221) | v2_struct_0(B_221) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(superposition, [status(thm), theory('equality')], [c_94, c_287])).
% 3.49/1.62  tff(c_402, plain, (![A_248, B_249, D_250, E_251]: (k3_tmap_1(A_248, B_249, '#skF_4', D_250, E_251)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_249), E_251, u1_struct_0(D_250)) | ~m1_pre_topc(D_250, '#skF_4') | ~m1_subset_1(E_251, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_249)))) | ~v1_funct_2(E_251, k2_struct_0('#skF_4'), u1_struct_0(B_249)) | ~v1_funct_1(E_251) | ~m1_pre_topc(D_250, A_248) | ~m1_pre_topc('#skF_4', A_248) | ~l1_pre_topc(B_249) | ~v2_pre_topc(B_249) | v2_struct_0(B_249) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_289])).
% 3.49/1.62  tff(c_406, plain, (![A_248, D_250, E_251]: (k3_tmap_1(A_248, '#skF_2', '#skF_4', D_250, E_251)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_251, u1_struct_0(D_250)) | ~m1_pre_topc(D_250, '#skF_4') | ~m1_subset_1(E_251, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_251, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_251) | ~m1_pre_topc(D_250, A_248) | ~m1_pre_topc('#skF_4', A_248) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(superposition, [status(thm), theory('equality')], [c_95, c_402])).
% 3.49/1.62  tff(c_411, plain, (![A_248, D_250, E_251]: (k3_tmap_1(A_248, '#skF_2', '#skF_4', D_250, E_251)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_251, u1_struct_0(D_250)) | ~m1_pre_topc(D_250, '#skF_4') | ~m1_subset_1(E_251, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_251, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_251) | ~m1_pre_topc(D_250, A_248) | ~m1_pre_topc('#skF_4', A_248) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_95, c_95, c_406])).
% 3.49/1.62  tff(c_414, plain, (![A_255, D_256, E_257]: (k3_tmap_1(A_255, '#skF_2', '#skF_4', D_256, E_257)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_257, u1_struct_0(D_256)) | ~m1_pre_topc(D_256, '#skF_4') | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_257, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_257) | ~m1_pre_topc(D_256, A_255) | ~m1_pre_topc('#skF_4', A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(negUnitSimplification, [status(thm)], [c_52, c_411])).
% 3.49/1.62  tff(c_416, plain, (![A_255, D_256]: (k3_tmap_1(A_255, '#skF_2', '#skF_4', D_256, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_256)) | ~m1_pre_topc(D_256, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_256, A_255) | ~m1_pre_topc('#skF_4', A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_111, c_414])).
% 3.49/1.62  tff(c_420, plain, (![D_258, A_259]: (k7_relat_1('#skF_5', u1_struct_0(D_258))=k3_tmap_1(A_259, '#skF_2', '#skF_4', D_258, '#skF_5') | ~m1_pre_topc(D_258, '#skF_4') | ~m1_pre_topc(D_258, A_259) | ~m1_pre_topc('#skF_4', A_259) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109, c_129, c_416])).
% 3.49/1.62  tff(c_422, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_420])).
% 3.49/1.62  tff(c_427, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_72, c_70, c_422])).
% 3.49/1.62  tff(c_428, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_427])).
% 3.49/1.62  tff(c_440, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_286, c_428])).
% 3.49/1.62  tff(c_446, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_440])).
% 3.49/1.62  tff(c_32, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_30, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_99, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_30])).
% 3.49/1.62  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_96, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_28])).
% 3.49/1.62  tff(c_161, plain, (![D_195, C_194, A_192, F_191, B_193]: (r1_funct_2(A_192, B_193, C_194, D_195, F_191, F_191) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(C_194, D_195))) | ~v1_funct_2(F_191, C_194, D_195) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2(F_191, A_192, B_193) | ~v1_funct_1(F_191) | v1_xboole_0(D_195) | v1_xboole_0(B_193))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.62  tff(c_163, plain, (![A_192, B_193]: (r1_funct_2(A_192, B_193, u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2('#skF_6', A_192, B_193) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_struct_0('#skF_2')) | v1_xboole_0(B_193))), inference(resolution, [status(thm)], [c_96, c_161])).
% 3.49/1.62  tff(c_170, plain, (![A_192, B_193]: (r1_funct_2(A_192, B_193, u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2('#skF_6', A_192, B_193) | v1_xboole_0(k2_struct_0('#skF_2')) | v1_xboole_0(B_193))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_99, c_163])).
% 3.49/1.62  tff(c_177, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_170])).
% 3.49/1.62  tff(c_8, plain, (![A_7]: (~v1_xboole_0(k2_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.62  tff(c_180, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_177, c_8])).
% 3.49/1.62  tff(c_183, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_180])).
% 3.49/1.62  tff(c_186, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_183])).
% 3.49/1.62  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_186])).
% 3.49/1.62  tff(c_192, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_170])).
% 3.49/1.62  tff(c_26, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_24, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_97, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_24])).
% 3.49/1.62  tff(c_108, plain, (v1_funct_2('#skF_7', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_97])).
% 3.49/1.62  tff(c_22, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_112, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_22])).
% 3.49/1.62  tff(c_18, plain, (r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_76, plain, (r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 3.49/1.62  tff(c_113, plain, (r1_funct_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_95, c_95, c_76])).
% 3.49/1.62  tff(c_196, plain, (![D_205, C_204, B_203, E_202, A_201, F_200]: (F_200=E_202 | ~r1_funct_2(A_201, B_203, C_204, D_205, E_202, F_200) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_204, D_205))) | ~v1_funct_2(F_200, C_204, D_205) | ~v1_funct_1(F_200) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_201, B_203))) | ~v1_funct_2(E_202, A_201, B_203) | ~v1_funct_1(E_202) | v1_xboole_0(D_205) | v1_xboole_0(B_203))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.62  tff(c_202, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_113, c_196])).
% 3.49/1.62  tff(c_215, plain, ('#skF_7'='#skF_5' | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109, c_111, c_26, c_108, c_112, c_202])).
% 3.49/1.62  tff(c_216, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_192, c_215])).
% 3.49/1.62  tff(c_60, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.49/1.62  tff(c_75, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_60])).
% 3.49/1.62  tff(c_157, plain, (~r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_95, c_75])).
% 3.49/1.62  tff(c_158, plain, (~r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_157])).
% 3.49/1.62  tff(c_218, plain, (~r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_158])).
% 3.49/1.62  tff(c_452, plain, (~r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_218])).
% 3.49/1.62  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_452])).
% 3.49/1.62  tff(c_456, plain, (r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_159])).
% 3.49/1.62  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_158])).
% 3.49/1.62  tff(c_460, plain, (~r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_157])).
% 3.49/1.62  tff(c_561, plain, (![A_283, B_284, C_285, D_286]: (k2_partfun1(u1_struct_0(A_283), u1_struct_0(B_284), C_285, u1_struct_0(D_286))=k2_tmap_1(A_283, B_284, C_285, D_286) | ~m1_pre_topc(D_286, A_283) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283), u1_struct_0(B_284)))) | ~v1_funct_2(C_285, u1_struct_0(A_283), u1_struct_0(B_284)) | ~v1_funct_1(C_285) | ~l1_pre_topc(B_284) | ~v2_pre_topc(B_284) | v2_struct_0(B_284) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.49/1.62  tff(c_563, plain, (![B_284, C_285, D_286]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_284), C_285, u1_struct_0(D_286))=k2_tmap_1('#skF_4', B_284, C_285, D_286) | ~m1_pre_topc(D_286, '#skF_4') | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_284)))) | ~v1_funct_2(C_285, u1_struct_0('#skF_4'), u1_struct_0(B_284)) | ~v1_funct_1(C_285) | ~l1_pre_topc(B_284) | ~v2_pre_topc(B_284) | v2_struct_0(B_284) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_561])).
% 3.49/1.62  tff(c_571, plain, (![B_284, C_285, D_286]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_284), C_285, u1_struct_0(D_286))=k2_tmap_1('#skF_4', B_284, C_285, D_286) | ~m1_pre_topc(D_286, '#skF_4') | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_284)))) | ~v1_funct_2(C_285, k2_struct_0('#skF_4'), u1_struct_0(B_284)) | ~v1_funct_1(C_285) | ~l1_pre_topc(B_284) | ~v2_pre_topc(B_284) | v2_struct_0(B_284) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_94, c_94, c_563])).
% 3.49/1.62  tff(c_582, plain, (![B_287, C_288, D_289]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_287), C_288, u1_struct_0(D_289))=k2_tmap_1('#skF_4', B_287, C_288, D_289) | ~m1_pre_topc(D_289, '#skF_4') | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_287)))) | ~v1_funct_2(C_288, k2_struct_0('#skF_4'), u1_struct_0(B_287)) | ~v1_funct_1(C_288) | ~l1_pre_topc(B_287) | ~v2_pre_topc(B_287) | v2_struct_0(B_287))), inference(negUnitSimplification, [status(thm)], [c_42, c_571])).
% 3.49/1.62  tff(c_586, plain, (![C_288, D_289]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_288, u1_struct_0(D_289))=k2_tmap_1('#skF_4', '#skF_2', C_288, D_289) | ~m1_pre_topc(D_289, '#skF_4') | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_288, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_288) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_582])).
% 3.49/1.62  tff(c_591, plain, (![C_288, D_289]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_288, u1_struct_0(D_289))=k2_tmap_1('#skF_4', '#skF_2', C_288, D_289) | ~m1_pre_topc(D_289, '#skF_4') | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_288, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_288) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_95, c_95, c_586])).
% 3.49/1.62  tff(c_594, plain, (![C_292, D_293]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_292, u1_struct_0(D_293))=k2_tmap_1('#skF_4', '#skF_2', C_292, D_293) | ~m1_pre_topc(D_293, '#skF_4') | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_292, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_292))), inference(negUnitSimplification, [status(thm)], [c_52, c_591])).
% 3.49/1.62  tff(c_596, plain, (![D_293]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_293))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_293) | ~m1_pre_topc(D_293, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_111, c_594])).
% 3.49/1.62  tff(c_599, plain, (![D_293]: (k7_relat_1('#skF_5', u1_struct_0(D_293))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_293) | ~m1_pre_topc(D_293, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109, c_129, c_596])).
% 3.49/1.62  tff(c_640, plain, (![D_301, E_302, A_299, B_300, C_298]: (k3_tmap_1(A_299, B_300, C_298, D_301, E_302)=k2_partfun1(u1_struct_0(C_298), u1_struct_0(B_300), E_302, u1_struct_0(D_301)) | ~m1_pre_topc(D_301, C_298) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298), u1_struct_0(B_300)))) | ~v1_funct_2(E_302, u1_struct_0(C_298), u1_struct_0(B_300)) | ~v1_funct_1(E_302) | ~m1_pre_topc(D_301, A_299) | ~m1_pre_topc(C_298, A_299) | ~l1_pre_topc(B_300) | ~v2_pre_topc(B_300) | v2_struct_0(B_300) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.49/1.62  tff(c_648, plain, (![A_299, C_298, D_301, E_302]: (k3_tmap_1(A_299, '#skF_2', C_298, D_301, E_302)=k2_partfun1(u1_struct_0(C_298), u1_struct_0('#skF_2'), E_302, u1_struct_0(D_301)) | ~m1_pre_topc(D_301, C_298) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_302, u1_struct_0(C_298), u1_struct_0('#skF_2')) | ~v1_funct_1(E_302) | ~m1_pre_topc(D_301, A_299) | ~m1_pre_topc(C_298, A_299) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(superposition, [status(thm), theory('equality')], [c_95, c_640])).
% 3.49/1.62  tff(c_655, plain, (![A_299, C_298, D_301, E_302]: (k3_tmap_1(A_299, '#skF_2', C_298, D_301, E_302)=k2_partfun1(u1_struct_0(C_298), k2_struct_0('#skF_2'), E_302, u1_struct_0(D_301)) | ~m1_pre_topc(D_301, C_298) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_302, u1_struct_0(C_298), k2_struct_0('#skF_2')) | ~v1_funct_1(E_302) | ~m1_pre_topc(D_301, A_299) | ~m1_pre_topc(C_298, A_299) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_95, c_95, c_648])).
% 3.49/1.62  tff(c_681, plain, (![A_313, C_314, D_315, E_316]: (k3_tmap_1(A_313, '#skF_2', C_314, D_315, E_316)=k2_partfun1(u1_struct_0(C_314), k2_struct_0('#skF_2'), E_316, u1_struct_0(D_315)) | ~m1_pre_topc(D_315, C_314) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_316, u1_struct_0(C_314), k2_struct_0('#skF_2')) | ~v1_funct_1(E_316) | ~m1_pre_topc(D_315, A_313) | ~m1_pre_topc(C_314, A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(negUnitSimplification, [status(thm)], [c_52, c_655])).
% 3.49/1.62  tff(c_685, plain, (![A_313, D_315, E_316]: (k3_tmap_1(A_313, '#skF_2', '#skF_4', D_315, E_316)=k2_partfun1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_316, u1_struct_0(D_315)) | ~m1_pre_topc(D_315, '#skF_4') | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_316, u1_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_316) | ~m1_pre_topc(D_315, A_313) | ~m1_pre_topc('#skF_4', A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(superposition, [status(thm), theory('equality')], [c_94, c_681])).
% 3.49/1.62  tff(c_718, plain, (![A_332, D_333, E_334]: (k3_tmap_1(A_332, '#skF_2', '#skF_4', D_333, E_334)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_334, u1_struct_0(D_333)) | ~m1_pre_topc(D_333, '#skF_4') | ~m1_subset_1(E_334, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_334, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_334) | ~m1_pre_topc(D_333, A_332) | ~m1_pre_topc('#skF_4', A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_685])).
% 3.49/1.62  tff(c_720, plain, (![A_332, D_333]: (k3_tmap_1(A_332, '#skF_2', '#skF_4', D_333, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_333)) | ~m1_pre_topc(D_333, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_333, A_332) | ~m1_pre_topc('#skF_4', A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(resolution, [status(thm)], [c_111, c_718])).
% 3.49/1.62  tff(c_724, plain, (![D_335, A_336]: (k7_relat_1('#skF_5', u1_struct_0(D_335))=k3_tmap_1(A_336, '#skF_2', '#skF_4', D_335, '#skF_5') | ~m1_pre_topc(D_335, '#skF_4') | ~m1_pre_topc(D_335, A_336) | ~m1_pre_topc('#skF_4', A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109, c_129, c_720])).
% 3.49/1.62  tff(c_726, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_724])).
% 3.49/1.62  tff(c_731, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_72, c_70, c_726])).
% 3.49/1.62  tff(c_732, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_731])).
% 3.49/1.62  tff(c_744, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_599, c_732])).
% 3.49/1.62  tff(c_750, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_744])).
% 3.49/1.62  tff(c_468, plain, (![F_260, D_264, C_263, B_262, A_261]: (r1_funct_2(A_261, B_262, C_263, D_264, F_260, F_260) | ~m1_subset_1(F_260, k1_zfmisc_1(k2_zfmisc_1(C_263, D_264))) | ~v1_funct_2(F_260, C_263, D_264) | ~m1_subset_1(F_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2(F_260, A_261, B_262) | ~v1_funct_1(F_260) | v1_xboole_0(D_264) | v1_xboole_0(B_262))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.62  tff(c_470, plain, (![A_261, B_262]: (r1_funct_2(A_261, B_262, u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2('#skF_6', A_261, B_262) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_struct_0('#skF_2')) | v1_xboole_0(B_262))), inference(resolution, [status(thm)], [c_96, c_468])).
% 3.49/1.62  tff(c_477, plain, (![A_261, B_262]: (r1_funct_2(A_261, B_262, u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2('#skF_6', A_261, B_262) | v1_xboole_0(k2_struct_0('#skF_2')) | v1_xboole_0(B_262))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_99, c_470])).
% 3.49/1.62  tff(c_484, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_477])).
% 3.49/1.62  tff(c_487, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_484, c_8])).
% 3.49/1.62  tff(c_490, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_487])).
% 3.49/1.62  tff(c_499, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_490])).
% 3.49/1.62  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_499])).
% 3.49/1.62  tff(c_505, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_477])).
% 3.49/1.62  tff(c_511, plain, (![F_277, A_278, B_280, C_281, D_282, E_279]: (F_277=E_279 | ~r1_funct_2(A_278, B_280, C_281, D_282, E_279, F_277) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(C_281, D_282))) | ~v1_funct_2(F_277, C_281, D_282) | ~v1_funct_1(F_277) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_278, B_280))) | ~v1_funct_2(E_279, A_278, B_280) | ~v1_funct_1(E_279) | v1_xboole_0(D_282) | v1_xboole_0(B_280))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.62  tff(c_519, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_113, c_511])).
% 3.49/1.62  tff(c_537, plain, ('#skF_7'='#skF_5' | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109, c_111, c_26, c_108, c_112, c_519])).
% 3.49/1.62  tff(c_538, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_505, c_537])).
% 3.49/1.62  tff(c_461, plain, (r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_157])).
% 3.49/1.62  tff(c_540, plain, (r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_461])).
% 3.49/1.62  tff(c_767, plain, (r2_funct_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_750, c_540])).
% 3.49/1.62  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_460, c_767])).
% 3.49/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.62  
% 3.49/1.62  Inference rules
% 3.49/1.62  ----------------------
% 3.49/1.62  #Ref     : 0
% 3.49/1.62  #Sup     : 127
% 3.49/1.62  #Fact    : 0
% 3.49/1.62  #Define  : 0
% 3.49/1.62  #Split   : 13
% 3.49/1.62  #Chain   : 0
% 3.49/1.62  #Close   : 0
% 3.49/1.62  
% 3.49/1.62  Ordering : KBO
% 3.49/1.62  
% 3.49/1.62  Simplification rules
% 3.49/1.62  ----------------------
% 3.49/1.62  #Subsume      : 14
% 3.49/1.62  #Demod        : 343
% 3.49/1.62  #Tautology    : 52
% 3.49/1.62  #SimpNegUnit  : 60
% 3.49/1.62  #BackRed      : 22
% 3.49/1.62  
% 3.49/1.62  #Partial instantiations: 0
% 3.49/1.62  #Strategies tried      : 1
% 3.49/1.62  
% 3.49/1.62  Timing (in seconds)
% 3.49/1.62  ----------------------
% 3.89/1.63  Preprocessing        : 0.38
% 3.89/1.63  Parsing              : 0.20
% 3.89/1.63  CNF conversion       : 0.05
% 3.89/1.63  Main loop            : 0.44
% 3.89/1.63  Inferencing          : 0.15
% 3.89/1.63  Reduction            : 0.17
% 3.89/1.63  Demodulation         : 0.12
% 3.89/1.63  BG Simplification    : 0.02
% 3.89/1.63  Subsumption          : 0.08
% 3.89/1.63  Abstraction          : 0.02
% 3.89/1.63  MUC search           : 0.00
% 3.89/1.63  Cooper               : 0.00
% 3.89/1.63  Total                : 0.88
% 3.89/1.63  Index Insertion      : 0.00
% 3.89/1.63  Index Deletion       : 0.00
% 3.89/1.63  Index Matching       : 0.00
% 3.89/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
