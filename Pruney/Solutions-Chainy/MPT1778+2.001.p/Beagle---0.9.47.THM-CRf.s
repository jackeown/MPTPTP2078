%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:43 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 560 expanded)
%              Number of leaves         :   31 ( 227 expanded)
%              Depth                    :   14
%              Number of atoms          :  598 (4301 expanded)
%              Number of equality atoms :   54 (  60 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_214,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ( m1_pre_topc(D,C)
                         => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
                            & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,C,D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_155,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & v5_pre_topc(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

tff(f_104,axiom,(
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

tff(f_72,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_77,plain,(
    ! [B_98,A_99] :
      ( v2_pre_topc(B_98)
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_95,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_86])).

tff(c_58,plain,(
    ! [B_96,A_97] :
      ( l1_pre_topc(B_96)
      | ~ m1_pre_topc(B_96,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_67])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_32,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_838,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( v5_pre_topc(k2_tmap_1(A_272,B_273,C_274,D_275),D_275,B_273)
      | ~ m1_pre_topc(D_275,A_272)
      | v2_struct_0(D_275)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_272),u1_struct_0(B_273))))
      | ~ v5_pre_topc(C_274,A_272,B_273)
      | ~ v1_funct_2(C_274,u1_struct_0(A_272),u1_struct_0(B_273))
      | ~ v1_funct_1(C_274)
      | ~ l1_pre_topc(B_273)
      | ~ v2_pre_topc(B_273)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_844,plain,(
    ! [D_275] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_275),D_275,'#skF_2')
      | ~ m1_pre_topc(D_275,'#skF_3')
      | v2_struct_0(D_275)
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_838])).

tff(c_852,plain,(
    ! [D_275] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_275),D_275,'#skF_2')
      | ~ m1_pre_topc(D_275,'#skF_3')
      | v2_struct_0(D_275)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_48,c_46,c_36,c_34,c_32,c_844])).

tff(c_853,plain,(
    ! [D_275] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_275),D_275,'#skF_2')
      | ~ m1_pre_topc(D_275,'#skF_3')
      | v2_struct_0(D_275) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_852])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_888,plain,(
    ! [C_290,B_289,A_291,D_288,E_287] :
      ( k3_tmap_1(A_291,B_289,C_290,D_288,E_287) = k2_partfun1(u1_struct_0(C_290),u1_struct_0(B_289),E_287,u1_struct_0(D_288))
      | ~ m1_pre_topc(D_288,C_290)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_290),u1_struct_0(B_289))))
      | ~ v1_funct_2(E_287,u1_struct_0(C_290),u1_struct_0(B_289))
      | ~ v1_funct_1(E_287)
      | ~ m1_pre_topc(D_288,A_291)
      | ~ m1_pre_topc(C_290,A_291)
      | ~ l1_pre_topc(B_289)
      | ~ v2_pre_topc(B_289)
      | v2_struct_0(B_289)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_894,plain,(
    ! [A_291,D_288] :
      ( k3_tmap_1(A_291,'#skF_2','#skF_3',D_288,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_288))
      | ~ m1_pre_topc(D_288,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_288,A_291)
      | ~ m1_pre_topc('#skF_3',A_291)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_30,c_888])).

tff(c_902,plain,(
    ! [A_291,D_288] :
      ( k3_tmap_1(A_291,'#skF_2','#skF_3',D_288,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_288))
      | ~ m1_pre_topc(D_288,'#skF_3')
      | ~ m1_pre_topc(D_288,A_291)
      | ~ m1_pre_topc('#skF_3',A_291)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_894])).

tff(c_905,plain,(
    ! [A_294,D_295] :
      ( k3_tmap_1(A_294,'#skF_2','#skF_3',D_295,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_295))
      | ~ m1_pre_topc(D_295,'#skF_3')
      | ~ m1_pre_topc(D_295,A_294)
      | ~ m1_pre_topc('#skF_3',A_294)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_902])).

tff(c_909,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_905])).

tff(c_917,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_28,c_909])).

tff(c_918,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_917])).

tff(c_804,plain,(
    ! [A_266,B_267,C_268,D_269] :
      ( k2_partfun1(u1_struct_0(A_266),u1_struct_0(B_267),C_268,u1_struct_0(D_269)) = k2_tmap_1(A_266,B_267,C_268,D_269)
      | ~ m1_pre_topc(D_269,A_266)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_266),u1_struct_0(B_267))))
      | ~ v1_funct_2(C_268,u1_struct_0(A_266),u1_struct_0(B_267))
      | ~ v1_funct_1(C_268)
      | ~ l1_pre_topc(B_267)
      | ~ v2_pre_topc(B_267)
      | v2_struct_0(B_267)
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_810,plain,(
    ! [D_269] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_269)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_269)
      | ~ m1_pre_topc(D_269,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_804])).

tff(c_818,plain,(
    ! [D_269] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_269)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_269)
      | ~ m1_pre_topc(D_269,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_48,c_46,c_36,c_34,c_810])).

tff(c_819,plain,(
    ! [D_269] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_269)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_269)
      | ~ m1_pre_topc(D_269,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_818])).

tff(c_930,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_819])).

tff(c_937,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_930])).

tff(c_652,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( v1_funct_2(k2_tmap_1(A_236,B_237,C_238,D_239),u1_struct_0(D_239),u1_struct_0(B_237))
      | ~ m1_pre_topc(D_239,A_236)
      | v2_struct_0(D_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_236),u1_struct_0(B_237))))
      | ~ v5_pre_topc(C_238,A_236,B_237)
      | ~ v1_funct_2(C_238,u1_struct_0(A_236),u1_struct_0(B_237))
      | ~ v1_funct_1(C_238)
      | ~ l1_pre_topc(B_237)
      | ~ v2_pre_topc(B_237)
      | v2_struct_0(B_237)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_658,plain,(
    ! [D_239] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_239),u1_struct_0(D_239),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_239,'#skF_3')
      | v2_struct_0(D_239)
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_652])).

tff(c_666,plain,(
    ! [D_239] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_239),u1_struct_0(D_239),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_239,'#skF_3')
      | v2_struct_0(D_239)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_48,c_46,c_36,c_34,c_32,c_658])).

tff(c_667,plain,(
    ! [D_239] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_239),u1_struct_0(D_239),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_239,'#skF_3')
      | v2_struct_0(D_239) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_666])).

tff(c_681,plain,(
    ! [A_252,B_250,D_249,E_248,C_251] :
      ( k3_tmap_1(A_252,B_250,C_251,D_249,E_248) = k2_partfun1(u1_struct_0(C_251),u1_struct_0(B_250),E_248,u1_struct_0(D_249))
      | ~ m1_pre_topc(D_249,C_251)
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251),u1_struct_0(B_250))))
      | ~ v1_funct_2(E_248,u1_struct_0(C_251),u1_struct_0(B_250))
      | ~ v1_funct_1(E_248)
      | ~ m1_pre_topc(D_249,A_252)
      | ~ m1_pre_topc(C_251,A_252)
      | ~ l1_pre_topc(B_250)
      | ~ v2_pre_topc(B_250)
      | v2_struct_0(B_250)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_687,plain,(
    ! [A_252,D_249] :
      ( k3_tmap_1(A_252,'#skF_2','#skF_3',D_249,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_249))
      | ~ m1_pre_topc(D_249,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_249,A_252)
      | ~ m1_pre_topc('#skF_3',A_252)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(resolution,[status(thm)],[c_30,c_681])).

tff(c_695,plain,(
    ! [A_252,D_249] :
      ( k3_tmap_1(A_252,'#skF_2','#skF_3',D_249,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_249))
      | ~ m1_pre_topc(D_249,'#skF_3')
      | ~ m1_pre_topc(D_249,A_252)
      | ~ m1_pre_topc('#skF_3',A_252)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_687])).

tff(c_697,plain,(
    ! [A_253,D_254] :
      ( k3_tmap_1(A_253,'#skF_2','#skF_3',D_254,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_254))
      | ~ m1_pre_topc(D_254,'#skF_3')
      | ~ m1_pre_topc(D_254,A_253)
      | ~ m1_pre_topc('#skF_3',A_253)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_695])).

tff(c_701,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_697])).

tff(c_709,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_28,c_701])).

tff(c_710,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_709])).

tff(c_610,plain,(
    ! [A_226,B_227,C_228,D_229] :
      ( k2_partfun1(u1_struct_0(A_226),u1_struct_0(B_227),C_228,u1_struct_0(D_229)) = k2_tmap_1(A_226,B_227,C_228,D_229)
      | ~ m1_pre_topc(D_229,A_226)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_226),u1_struct_0(B_227))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_226),u1_struct_0(B_227))
      | ~ v1_funct_1(C_228)
      | ~ l1_pre_topc(B_227)
      | ~ v2_pre_topc(B_227)
      | v2_struct_0(B_227)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_616,plain,(
    ! [D_229] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_229)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_229)
      | ~ m1_pre_topc(D_229,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_610])).

tff(c_624,plain,(
    ! [D_229] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_229)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_229)
      | ~ m1_pre_topc(D_229,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_48,c_46,c_36,c_34,c_616])).

tff(c_625,plain,(
    ! [D_229] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_229)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_229)
      | ~ m1_pre_topc(D_229,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_624])).

tff(c_722,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_625])).

tff(c_729,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_722])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_61])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( v1_funct_1(k2_tmap_1(A_103,B_104,C_105,D_106))
      | ~ l1_struct_0(D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,u1_struct_0(A_103),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_struct_0(B_104)
      | ~ l1_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_110,plain,(
    ! [D_106] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_106))
      | ~ l1_struct_0(D_106)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_113,plain,(
    ! [D_106] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_106))
      | ~ l1_struct_0(D_106)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_110])).

tff(c_346,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_349,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_346])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_349])).

tff(c_355,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_354,plain,(
    ! [D_106] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_106))
      | ~ l1_struct_0(D_106) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_357,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_360,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_357])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_360])).

tff(c_366,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_12,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( m1_subset_1(k2_tmap_1(A_54,B_55,C_56,D_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_57),u1_struct_0(B_55))))
      | ~ l1_struct_0(D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54),u1_struct_0(B_55))))
      | ~ v1_funct_2(C_56,u1_struct_0(A_54),u1_struct_0(B_55))
      | ~ v1_funct_1(C_56)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_465,plain,(
    ! [E_201,C_204,B_203,A_205,D_202] :
      ( k3_tmap_1(A_205,B_203,C_204,D_202,E_201) = k2_partfun1(u1_struct_0(C_204),u1_struct_0(B_203),E_201,u1_struct_0(D_202))
      | ~ m1_pre_topc(D_202,C_204)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204),u1_struct_0(B_203))))
      | ~ v1_funct_2(E_201,u1_struct_0(C_204),u1_struct_0(B_203))
      | ~ v1_funct_1(E_201)
      | ~ m1_pre_topc(D_202,A_205)
      | ~ m1_pre_topc(C_204,A_205)
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_469,plain,(
    ! [A_205,D_202] :
      ( k3_tmap_1(A_205,'#skF_2','#skF_3',D_202,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_202))
      | ~ m1_pre_topc(D_202,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_202,A_205)
      | ~ m1_pre_topc('#skF_3',A_205)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(resolution,[status(thm)],[c_30,c_465])).

tff(c_473,plain,(
    ! [A_205,D_202] :
      ( k3_tmap_1(A_205,'#skF_2','#skF_3',D_202,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_202))
      | ~ m1_pre_topc(D_202,'#skF_3')
      | ~ m1_pre_topc(D_202,A_205)
      | ~ m1_pre_topc('#skF_3',A_205)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_469])).

tff(c_475,plain,(
    ! [A_206,D_207] :
      ( k3_tmap_1(A_206,'#skF_2','#skF_3',D_207,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_207))
      | ~ m1_pre_topc(D_207,'#skF_3')
      | ~ m1_pre_topc(D_207,A_206)
      | ~ m1_pre_topc('#skF_3',A_206)
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_473])).

tff(c_479,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_475])).

tff(c_487,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_28,c_479])).

tff(c_488,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_487])).

tff(c_411,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k2_partfun1(u1_struct_0(A_177),u1_struct_0(B_178),C_179,u1_struct_0(D_180)) = k2_tmap_1(A_177,B_178,C_179,D_180)
      | ~ m1_pre_topc(D_180,A_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177),u1_struct_0(B_178))))
      | ~ v1_funct_2(C_179,u1_struct_0(A_177),u1_struct_0(B_178))
      | ~ v1_funct_1(C_179)
      | ~ l1_pre_topc(B_178)
      | ~ v2_pre_topc(B_178)
      | v2_struct_0(B_178)
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_415,plain,(
    ! [D_180] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_180)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_180)
      | ~ m1_pre_topc(D_180,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_411])).

tff(c_419,plain,(
    ! [D_180] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_180)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_180)
      | ~ m1_pre_topc(D_180,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_48,c_46,c_36,c_34,c_415])).

tff(c_420,plain,(
    ! [D_180] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_180)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_180)
      | ~ m1_pre_topc(D_180,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_419])).

tff(c_500,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_420])).

tff(c_507,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_500])).

tff(c_204,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( v1_funct_1(k2_tmap_1(A_126,B_127,C_128,D_129))
      | ~ m1_pre_topc(D_129,A_126)
      | v2_struct_0(D_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126),u1_struct_0(B_127))))
      | ~ v5_pre_topc(C_128,A_126,B_127)
      | ~ v1_funct_2(C_128,u1_struct_0(A_126),u1_struct_0(B_127))
      | ~ v1_funct_1(C_128)
      | ~ l1_pre_topc(B_127)
      | ~ v2_pre_topc(B_127)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_208,plain,(
    ! [D_129] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_129))
      | ~ m1_pre_topc(D_129,'#skF_3')
      | v2_struct_0(D_129)
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_204])).

tff(c_212,plain,(
    ! [D_129] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_129))
      | ~ m1_pre_topc(D_129,'#skF_3')
      | v2_struct_0(D_129)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_48,c_46,c_36,c_34,c_32,c_208])).

tff(c_213,plain,(
    ! [D_129] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_129))
      | ~ m1_pre_topc(D_129,'#skF_3')
      | v2_struct_0(D_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_212])).

tff(c_268,plain,(
    ! [B_155,C_156,E_153,A_157,D_154] :
      ( k3_tmap_1(A_157,B_155,C_156,D_154,E_153) = k2_partfun1(u1_struct_0(C_156),u1_struct_0(B_155),E_153,u1_struct_0(D_154))
      | ~ m1_pre_topc(D_154,C_156)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_156),u1_struct_0(B_155))))
      | ~ v1_funct_2(E_153,u1_struct_0(C_156),u1_struct_0(B_155))
      | ~ v1_funct_1(E_153)
      | ~ m1_pre_topc(D_154,A_157)
      | ~ m1_pre_topc(C_156,A_157)
      | ~ l1_pre_topc(B_155)
      | ~ v2_pre_topc(B_155)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_272,plain,(
    ! [A_157,D_154] :
      ( k3_tmap_1(A_157,'#skF_2','#skF_3',D_154,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_154))
      | ~ m1_pre_topc(D_154,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_154,A_157)
      | ~ m1_pre_topc('#skF_3',A_157)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_30,c_268])).

tff(c_276,plain,(
    ! [A_157,D_154] :
      ( k3_tmap_1(A_157,'#skF_2','#skF_3',D_154,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_154))
      | ~ m1_pre_topc(D_154,'#skF_3')
      | ~ m1_pre_topc(D_154,A_157)
      | ~ m1_pre_topc('#skF_3',A_157)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_272])).

tff(c_278,plain,(
    ! [A_158,D_159] :
      ( k3_tmap_1(A_158,'#skF_2','#skF_3',D_159,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_159))
      | ~ m1_pre_topc(D_159,'#skF_3')
      | ~ m1_pre_topc(D_159,A_158)
      | ~ m1_pre_topc('#skF_3',A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_276])).

tff(c_282,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_278])).

tff(c_290,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_28,c_282])).

tff(c_291,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_290])).

tff(c_215,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k2_partfun1(u1_struct_0(A_131),u1_struct_0(B_132),C_133,u1_struct_0(D_134)) = k2_tmap_1(A_131,B_132,C_133,D_134)
      | ~ m1_pre_topc(D_134,A_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(B_132))))
      | ~ v1_funct_2(C_133,u1_struct_0(A_131),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_219,plain,(
    ! [D_134] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_134)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_134)
      | ~ m1_pre_topc(D_134,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_215])).

tff(c_223,plain,(
    ! [D_134] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_134)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_134)
      | ~ m1_pre_topc(D_134,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_48,c_46,c_36,c_34,c_219])).

tff(c_224,plain,(
    ! [D_134] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_134)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_134)
      | ~ m1_pre_topc(D_134,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_223])).

tff(c_303,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_224])).

tff(c_310,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_303])).

tff(c_26,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_140,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_322,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_140])).

tff(c_329,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_213,c_322])).

tff(c_335,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_329])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_335])).

tff(c_338,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_356,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_512,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_356])).

tff(c_525,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_512])).

tff(c_528,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_366,c_36,c_34,c_30,c_525])).

tff(c_532,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_528])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_532])).

tff(c_537,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_585,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_537])).

tff(c_741,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_585])).

tff(c_750,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_667,c_741])).

tff(c_756,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_750])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_756])).

tff(c_759,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_946,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_937,c_759])).

tff(c_955,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_853,c_946])).

tff(c_958,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_955])).

tff(c_960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_958])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n025.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 12:02:35 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.65  
% 3.85/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.66  %$ v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.66  
% 3.85/1.66  %Foreground sorts:
% 3.85/1.66  
% 3.85/1.66  
% 3.85/1.66  %Background operators:
% 3.85/1.66  
% 3.85/1.66  
% 3.85/1.66  %Foreground operators:
% 3.85/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.85/1.66  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.66  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.85/1.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.85/1.66  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.85/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.66  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.85/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.66  
% 3.85/1.68  tff(f_214, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, C, D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_tmap_1)).
% 3.85/1.68  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.85/1.68  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.85/1.68  tff(f_155, axiom, (![A, B, C, D]: ((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tmap_1)).
% 3.85/1.68  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.85/1.68  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.85/1.68  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.85/1.68  tff(f_122, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 3.85/1.68  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_77, plain, (![B_98, A_99]: (v2_pre_topc(B_98) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.85/1.68  tff(c_86, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_77])).
% 3.85/1.68  tff(c_95, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_86])).
% 3.85/1.68  tff(c_58, plain, (![B_96, A_97]: (l1_pre_topc(B_96) | ~m1_pre_topc(B_96, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.85/1.68  tff(c_67, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_58])).
% 3.85/1.68  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_67])).
% 3.85/1.68  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_32, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_838, plain, (![A_272, B_273, C_274, D_275]: (v5_pre_topc(k2_tmap_1(A_272, B_273, C_274, D_275), D_275, B_273) | ~m1_pre_topc(D_275, A_272) | v2_struct_0(D_275) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_272), u1_struct_0(B_273)))) | ~v5_pre_topc(C_274, A_272, B_273) | ~v1_funct_2(C_274, u1_struct_0(A_272), u1_struct_0(B_273)) | ~v1_funct_1(C_274) | ~l1_pre_topc(B_273) | ~v2_pre_topc(B_273) | v2_struct_0(B_273) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/1.68  tff(c_844, plain, (![D_275]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_275), D_275, '#skF_2') | ~m1_pre_topc(D_275, '#skF_3') | v2_struct_0(D_275) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_838])).
% 3.85/1.68  tff(c_852, plain, (![D_275]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_275), D_275, '#skF_2') | ~m1_pre_topc(D_275, '#skF_3') | v2_struct_0(D_275) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_74, c_48, c_46, c_36, c_34, c_32, c_844])).
% 3.85/1.68  tff(c_853, plain, (![D_275]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_275), D_275, '#skF_2') | ~m1_pre_topc(D_275, '#skF_3') | v2_struct_0(D_275))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_852])).
% 3.85/1.68  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_888, plain, (![C_290, B_289, A_291, D_288, E_287]: (k3_tmap_1(A_291, B_289, C_290, D_288, E_287)=k2_partfun1(u1_struct_0(C_290), u1_struct_0(B_289), E_287, u1_struct_0(D_288)) | ~m1_pre_topc(D_288, C_290) | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_290), u1_struct_0(B_289)))) | ~v1_funct_2(E_287, u1_struct_0(C_290), u1_struct_0(B_289)) | ~v1_funct_1(E_287) | ~m1_pre_topc(D_288, A_291) | ~m1_pre_topc(C_290, A_291) | ~l1_pre_topc(B_289) | ~v2_pre_topc(B_289) | v2_struct_0(B_289) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.68  tff(c_894, plain, (![A_291, D_288]: (k3_tmap_1(A_291, '#skF_2', '#skF_3', D_288, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_288)) | ~m1_pre_topc(D_288, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_288, A_291) | ~m1_pre_topc('#skF_3', A_291) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(resolution, [status(thm)], [c_30, c_888])).
% 3.85/1.68  tff(c_902, plain, (![A_291, D_288]: (k3_tmap_1(A_291, '#skF_2', '#skF_3', D_288, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_288)) | ~m1_pre_topc(D_288, '#skF_3') | ~m1_pre_topc(D_288, A_291) | ~m1_pre_topc('#skF_3', A_291) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_894])).
% 3.85/1.68  tff(c_905, plain, (![A_294, D_295]: (k3_tmap_1(A_294, '#skF_2', '#skF_3', D_295, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_295)) | ~m1_pre_topc(D_295, '#skF_3') | ~m1_pre_topc(D_295, A_294) | ~m1_pre_topc('#skF_3', A_294) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(negUnitSimplification, [status(thm)], [c_50, c_902])).
% 3.85/1.68  tff(c_909, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_905])).
% 3.85/1.68  tff(c_917, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_28, c_909])).
% 3.85/1.68  tff(c_918, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_917])).
% 3.85/1.68  tff(c_804, plain, (![A_266, B_267, C_268, D_269]: (k2_partfun1(u1_struct_0(A_266), u1_struct_0(B_267), C_268, u1_struct_0(D_269))=k2_tmap_1(A_266, B_267, C_268, D_269) | ~m1_pre_topc(D_269, A_266) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_266), u1_struct_0(B_267)))) | ~v1_funct_2(C_268, u1_struct_0(A_266), u1_struct_0(B_267)) | ~v1_funct_1(C_268) | ~l1_pre_topc(B_267) | ~v2_pre_topc(B_267) | v2_struct_0(B_267) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266) | v2_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_810, plain, (![D_269]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_269))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_269) | ~m1_pre_topc(D_269, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_804])).
% 3.85/1.68  tff(c_818, plain, (![D_269]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_269))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_269) | ~m1_pre_topc(D_269, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_74, c_48, c_46, c_36, c_34, c_810])).
% 3.85/1.68  tff(c_819, plain, (![D_269]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_269))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_269) | ~m1_pre_topc(D_269, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_818])).
% 3.85/1.68  tff(c_930, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_918, c_819])).
% 3.85/1.68  tff(c_937, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_930])).
% 3.85/1.68  tff(c_652, plain, (![A_236, B_237, C_238, D_239]: (v1_funct_2(k2_tmap_1(A_236, B_237, C_238, D_239), u1_struct_0(D_239), u1_struct_0(B_237)) | ~m1_pre_topc(D_239, A_236) | v2_struct_0(D_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_236), u1_struct_0(B_237)))) | ~v5_pre_topc(C_238, A_236, B_237) | ~v1_funct_2(C_238, u1_struct_0(A_236), u1_struct_0(B_237)) | ~v1_funct_1(C_238) | ~l1_pre_topc(B_237) | ~v2_pre_topc(B_237) | v2_struct_0(B_237) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/1.68  tff(c_658, plain, (![D_239]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_239), u1_struct_0(D_239), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_239, '#skF_3') | v2_struct_0(D_239) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_652])).
% 3.85/1.68  tff(c_666, plain, (![D_239]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_239), u1_struct_0(D_239), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_239, '#skF_3') | v2_struct_0(D_239) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_74, c_48, c_46, c_36, c_34, c_32, c_658])).
% 3.85/1.68  tff(c_667, plain, (![D_239]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_239), u1_struct_0(D_239), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_239, '#skF_3') | v2_struct_0(D_239))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_666])).
% 3.85/1.68  tff(c_681, plain, (![A_252, B_250, D_249, E_248, C_251]: (k3_tmap_1(A_252, B_250, C_251, D_249, E_248)=k2_partfun1(u1_struct_0(C_251), u1_struct_0(B_250), E_248, u1_struct_0(D_249)) | ~m1_pre_topc(D_249, C_251) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251), u1_struct_0(B_250)))) | ~v1_funct_2(E_248, u1_struct_0(C_251), u1_struct_0(B_250)) | ~v1_funct_1(E_248) | ~m1_pre_topc(D_249, A_252) | ~m1_pre_topc(C_251, A_252) | ~l1_pre_topc(B_250) | ~v2_pre_topc(B_250) | v2_struct_0(B_250) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.68  tff(c_687, plain, (![A_252, D_249]: (k3_tmap_1(A_252, '#skF_2', '#skF_3', D_249, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_249)) | ~m1_pre_topc(D_249, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_249, A_252) | ~m1_pre_topc('#skF_3', A_252) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(resolution, [status(thm)], [c_30, c_681])).
% 3.85/1.68  tff(c_695, plain, (![A_252, D_249]: (k3_tmap_1(A_252, '#skF_2', '#skF_3', D_249, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_249)) | ~m1_pre_topc(D_249, '#skF_3') | ~m1_pre_topc(D_249, A_252) | ~m1_pre_topc('#skF_3', A_252) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_687])).
% 3.85/1.68  tff(c_697, plain, (![A_253, D_254]: (k3_tmap_1(A_253, '#skF_2', '#skF_3', D_254, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_254)) | ~m1_pre_topc(D_254, '#skF_3') | ~m1_pre_topc(D_254, A_253) | ~m1_pre_topc('#skF_3', A_253) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(negUnitSimplification, [status(thm)], [c_50, c_695])).
% 3.85/1.68  tff(c_701, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_697])).
% 3.85/1.68  tff(c_709, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_28, c_701])).
% 3.85/1.68  tff(c_710, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_709])).
% 3.85/1.68  tff(c_610, plain, (![A_226, B_227, C_228, D_229]: (k2_partfun1(u1_struct_0(A_226), u1_struct_0(B_227), C_228, u1_struct_0(D_229))=k2_tmap_1(A_226, B_227, C_228, D_229) | ~m1_pre_topc(D_229, A_226) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_226), u1_struct_0(B_227)))) | ~v1_funct_2(C_228, u1_struct_0(A_226), u1_struct_0(B_227)) | ~v1_funct_1(C_228) | ~l1_pre_topc(B_227) | ~v2_pre_topc(B_227) | v2_struct_0(B_227) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_616, plain, (![D_229]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_229))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_229) | ~m1_pre_topc(D_229, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_610])).
% 3.85/1.68  tff(c_624, plain, (![D_229]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_229))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_229) | ~m1_pre_topc(D_229, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_74, c_48, c_46, c_36, c_34, c_616])).
% 3.85/1.68  tff(c_625, plain, (![D_229]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_229))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_229) | ~m1_pre_topc(D_229, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_624])).
% 3.85/1.68  tff(c_722, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_710, c_625])).
% 3.85/1.68  tff(c_729, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_722])).
% 3.85/1.68  tff(c_61, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_58])).
% 3.85/1.68  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_61])).
% 3.85/1.68  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.68  tff(c_108, plain, (![A_103, B_104, C_105, D_106]: (v1_funct_1(k2_tmap_1(A_103, B_104, C_105, D_106)) | ~l1_struct_0(D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, u1_struct_0(A_103), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_struct_0(B_104) | ~l1_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.68  tff(c_110, plain, (![D_106]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_106)) | ~l1_struct_0(D_106) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_108])).
% 3.85/1.68  tff(c_113, plain, (![D_106]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_106)) | ~l1_struct_0(D_106) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_110])).
% 3.85/1.68  tff(c_346, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_113])).
% 3.85/1.68  tff(c_349, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_346])).
% 3.85/1.68  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_349])).
% 3.85/1.68  tff(c_355, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_113])).
% 3.85/1.68  tff(c_354, plain, (![D_106]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_106)) | ~l1_struct_0(D_106))), inference(splitRight, [status(thm)], [c_113])).
% 3.85/1.68  tff(c_357, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_354])).
% 3.85/1.68  tff(c_360, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_357])).
% 3.85/1.68  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_360])).
% 3.85/1.68  tff(c_366, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_354])).
% 3.85/1.68  tff(c_12, plain, (![A_54, B_55, C_56, D_57]: (m1_subset_1(k2_tmap_1(A_54, B_55, C_56, D_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_57), u1_struct_0(B_55)))) | ~l1_struct_0(D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54), u1_struct_0(B_55)))) | ~v1_funct_2(C_56, u1_struct_0(A_54), u1_struct_0(B_55)) | ~v1_funct_1(C_56) | ~l1_struct_0(B_55) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.68  tff(c_465, plain, (![E_201, C_204, B_203, A_205, D_202]: (k3_tmap_1(A_205, B_203, C_204, D_202, E_201)=k2_partfun1(u1_struct_0(C_204), u1_struct_0(B_203), E_201, u1_struct_0(D_202)) | ~m1_pre_topc(D_202, C_204) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204), u1_struct_0(B_203)))) | ~v1_funct_2(E_201, u1_struct_0(C_204), u1_struct_0(B_203)) | ~v1_funct_1(E_201) | ~m1_pre_topc(D_202, A_205) | ~m1_pre_topc(C_204, A_205) | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.68  tff(c_469, plain, (![A_205, D_202]: (k3_tmap_1(A_205, '#skF_2', '#skF_3', D_202, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_202)) | ~m1_pre_topc(D_202, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_202, A_205) | ~m1_pre_topc('#skF_3', A_205) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(resolution, [status(thm)], [c_30, c_465])).
% 3.85/1.68  tff(c_473, plain, (![A_205, D_202]: (k3_tmap_1(A_205, '#skF_2', '#skF_3', D_202, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_202)) | ~m1_pre_topc(D_202, '#skF_3') | ~m1_pre_topc(D_202, A_205) | ~m1_pre_topc('#skF_3', A_205) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_469])).
% 3.85/1.68  tff(c_475, plain, (![A_206, D_207]: (k3_tmap_1(A_206, '#skF_2', '#skF_3', D_207, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_207)) | ~m1_pre_topc(D_207, '#skF_3') | ~m1_pre_topc(D_207, A_206) | ~m1_pre_topc('#skF_3', A_206) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(negUnitSimplification, [status(thm)], [c_50, c_473])).
% 3.85/1.68  tff(c_479, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_475])).
% 3.85/1.68  tff(c_487, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_28, c_479])).
% 3.85/1.68  tff(c_488, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_487])).
% 3.85/1.68  tff(c_411, plain, (![A_177, B_178, C_179, D_180]: (k2_partfun1(u1_struct_0(A_177), u1_struct_0(B_178), C_179, u1_struct_0(D_180))=k2_tmap_1(A_177, B_178, C_179, D_180) | ~m1_pre_topc(D_180, A_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177), u1_struct_0(B_178)))) | ~v1_funct_2(C_179, u1_struct_0(A_177), u1_struct_0(B_178)) | ~v1_funct_1(C_179) | ~l1_pre_topc(B_178) | ~v2_pre_topc(B_178) | v2_struct_0(B_178) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_415, plain, (![D_180]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_180))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_180) | ~m1_pre_topc(D_180, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_411])).
% 3.85/1.68  tff(c_419, plain, (![D_180]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_180))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_180) | ~m1_pre_topc(D_180, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_74, c_48, c_46, c_36, c_34, c_415])).
% 3.85/1.68  tff(c_420, plain, (![D_180]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_180))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_180) | ~m1_pre_topc(D_180, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_419])).
% 3.85/1.68  tff(c_500, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_488, c_420])).
% 3.85/1.68  tff(c_507, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_500])).
% 3.85/1.68  tff(c_204, plain, (![A_126, B_127, C_128, D_129]: (v1_funct_1(k2_tmap_1(A_126, B_127, C_128, D_129)) | ~m1_pre_topc(D_129, A_126) | v2_struct_0(D_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126), u1_struct_0(B_127)))) | ~v5_pre_topc(C_128, A_126, B_127) | ~v1_funct_2(C_128, u1_struct_0(A_126), u1_struct_0(B_127)) | ~v1_funct_1(C_128) | ~l1_pre_topc(B_127) | ~v2_pre_topc(B_127) | v2_struct_0(B_127) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/1.68  tff(c_208, plain, (![D_129]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_129)) | ~m1_pre_topc(D_129, '#skF_3') | v2_struct_0(D_129) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_204])).
% 3.85/1.68  tff(c_212, plain, (![D_129]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_129)) | ~m1_pre_topc(D_129, '#skF_3') | v2_struct_0(D_129) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_74, c_48, c_46, c_36, c_34, c_32, c_208])).
% 3.85/1.68  tff(c_213, plain, (![D_129]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_129)) | ~m1_pre_topc(D_129, '#skF_3') | v2_struct_0(D_129))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_212])).
% 3.85/1.68  tff(c_268, plain, (![B_155, C_156, E_153, A_157, D_154]: (k3_tmap_1(A_157, B_155, C_156, D_154, E_153)=k2_partfun1(u1_struct_0(C_156), u1_struct_0(B_155), E_153, u1_struct_0(D_154)) | ~m1_pre_topc(D_154, C_156) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_156), u1_struct_0(B_155)))) | ~v1_funct_2(E_153, u1_struct_0(C_156), u1_struct_0(B_155)) | ~v1_funct_1(E_153) | ~m1_pre_topc(D_154, A_157) | ~m1_pre_topc(C_156, A_157) | ~l1_pre_topc(B_155) | ~v2_pre_topc(B_155) | v2_struct_0(B_155) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.68  tff(c_272, plain, (![A_157, D_154]: (k3_tmap_1(A_157, '#skF_2', '#skF_3', D_154, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_154)) | ~m1_pre_topc(D_154, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_154, A_157) | ~m1_pre_topc('#skF_3', A_157) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_30, c_268])).
% 3.85/1.68  tff(c_276, plain, (![A_157, D_154]: (k3_tmap_1(A_157, '#skF_2', '#skF_3', D_154, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_154)) | ~m1_pre_topc(D_154, '#skF_3') | ~m1_pre_topc(D_154, A_157) | ~m1_pre_topc('#skF_3', A_157) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_272])).
% 3.85/1.68  tff(c_278, plain, (![A_158, D_159]: (k3_tmap_1(A_158, '#skF_2', '#skF_3', D_159, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_159)) | ~m1_pre_topc(D_159, '#skF_3') | ~m1_pre_topc(D_159, A_158) | ~m1_pre_topc('#skF_3', A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(negUnitSimplification, [status(thm)], [c_50, c_276])).
% 3.85/1.68  tff(c_282, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_278])).
% 3.85/1.68  tff(c_290, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_28, c_282])).
% 3.85/1.68  tff(c_291, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_290])).
% 3.85/1.68  tff(c_215, plain, (![A_131, B_132, C_133, D_134]: (k2_partfun1(u1_struct_0(A_131), u1_struct_0(B_132), C_133, u1_struct_0(D_134))=k2_tmap_1(A_131, B_132, C_133, D_134) | ~m1_pre_topc(D_134, A_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131), u1_struct_0(B_132)))) | ~v1_funct_2(C_133, u1_struct_0(A_131), u1_struct_0(B_132)) | ~v1_funct_1(C_133) | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.68  tff(c_219, plain, (![D_134]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_134))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_134) | ~m1_pre_topc(D_134, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_215])).
% 3.85/1.68  tff(c_223, plain, (![D_134]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_134))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_134) | ~m1_pre_topc(D_134, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_74, c_48, c_46, c_36, c_34, c_219])).
% 3.85/1.68  tff(c_224, plain, (![D_134]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_134))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_134) | ~m1_pre_topc(D_134, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_223])).
% 3.85/1.68  tff(c_303, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_291, c_224])).
% 3.85/1.68  tff(c_310, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_303])).
% 3.85/1.68  tff(c_26, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.85/1.68  tff(c_140, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_26])).
% 3.85/1.68  tff(c_322, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_140])).
% 3.85/1.68  tff(c_329, plain, (~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_213, c_322])).
% 3.85/1.68  tff(c_335, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_329])).
% 3.85/1.68  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_335])).
% 3.85/1.68  tff(c_338, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_26])).
% 3.85/1.68  tff(c_356, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_338])).
% 3.85/1.68  tff(c_512, plain, (~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_356])).
% 3.85/1.68  tff(c_525, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_512])).
% 3.85/1.68  tff(c_528, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_366, c_36, c_34, c_30, c_525])).
% 3.85/1.68  tff(c_532, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_528])).
% 3.85/1.68  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_532])).
% 3.85/1.68  tff(c_537, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_338])).
% 3.85/1.68  tff(c_585, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_537])).
% 3.85/1.68  tff(c_741, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_729, c_585])).
% 3.85/1.68  tff(c_750, plain, (~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_667, c_741])).
% 3.85/1.68  tff(c_756, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_750])).
% 3.85/1.68  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_756])).
% 3.85/1.68  tff(c_759, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_537])).
% 3.85/1.68  tff(c_946, plain, (~v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_937, c_759])).
% 3.85/1.68  tff(c_955, plain, (~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_853, c_946])).
% 3.85/1.68  tff(c_958, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_955])).
% 3.85/1.68  tff(c_960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_958])).
% 3.85/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.68  
% 3.85/1.68  Inference rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Ref     : 0
% 3.85/1.68  #Sup     : 165
% 3.85/1.68  #Fact    : 0
% 3.85/1.68  #Define  : 0
% 3.85/1.68  #Split   : 16
% 3.85/1.68  #Chain   : 0
% 3.85/1.68  #Close   : 0
% 3.85/1.68  
% 3.85/1.68  Ordering : KBO
% 3.85/1.68  
% 3.85/1.68  Simplification rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Subsume      : 18
% 3.85/1.68  #Demod        : 393
% 3.85/1.68  #Tautology    : 38
% 3.85/1.68  #SimpNegUnit  : 45
% 3.85/1.68  #BackRed      : 17
% 3.85/1.68  
% 3.85/1.68  #Partial instantiations: 0
% 3.85/1.68  #Strategies tried      : 1
% 3.85/1.68  
% 3.85/1.68  Timing (in seconds)
% 3.85/1.68  ----------------------
% 4.13/1.69  Preprocessing        : 0.37
% 4.13/1.69  Parsing              : 0.21
% 4.13/1.69  CNF conversion       : 0.04
% 4.13/1.69  Main loop            : 0.51
% 4.13/1.69  Inferencing          : 0.19
% 4.13/1.69  Reduction            : 0.16
% 4.13/1.69  Demodulation         : 0.12
% 4.13/1.69  BG Simplification    : 0.03
% 4.13/1.69  Subsumption          : 0.10
% 4.13/1.69  Abstraction          : 0.02
% 4.13/1.69  MUC search           : 0.00
% 4.13/1.69  Cooper               : 0.00
% 4.13/1.69  Total                : 0.92
% 4.13/1.69  Index Insertion      : 0.00
% 4.13/1.69  Index Deletion       : 0.00
% 4.13/1.69  Index Matching       : 0.00
% 4.13/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
