%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1795+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:24 EST 2020

% Result     : Theorem 12.63s
% Output     : CNFRefutation 12.94s
% Verified   : 
% Statistics : Number of formulae       :  250 (3575 expanded)
%              Number of leaves         :   46 (1297 expanded)
%              Depth                    :   22
%              Number of atoms          :  753 (16642 expanded)
%              Number of equality atoms :   57 ( 995 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v1_partfun1 > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_234,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_xboole_0(u1_struct_0(C),B)
                 => ( v1_funct_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C))
                    & v1_funct_2(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B)))
                    & v5_pre_topc(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),C,k6_tmap_1(A,B))
                    & m1_subset_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tmap_1)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_207,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_xboole_0(u1_struct_0(C),B)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1505,plain,(
    ! [B_224,A_225] :
      ( l1_pre_topc(B_224)
      | ~ m1_pre_topc(B_224,A_225)
      | ~ l1_pre_topc(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1508,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1505])).

tff(c_1511,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1508])).

tff(c_32,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1580,plain,(
    ! [A_247,B_248] :
      ( v1_funct_1(k7_tmap_1(A_247,B_248))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1583,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1580])).

tff(c_1586,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1583])).

tff(c_1587,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1586])).

tff(c_1564,plain,(
    ! [A_243,B_244] :
      ( l1_pre_topc(k6_tmap_1(A_243,B_244))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1567,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1564])).

tff(c_1570,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1567])).

tff(c_1571,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1570])).

tff(c_1572,plain,(
    ! [A_245,B_246] :
      ( v1_pre_topc(k6_tmap_1(A_245,B_246))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1575,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1572])).

tff(c_1578,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1575])).

tff(c_1579,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1578])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ! [A_24] :
      ( m1_subset_1(u1_pre_topc(A_24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_24))))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8299,plain,(
    ! [A_721,B_722] :
      ( g1_pre_topc(u1_struct_0(A_721),k5_tmap_1(A_721,B_722)) = k6_tmap_1(A_721,B_722)
      | ~ m1_subset_1(B_722,k1_zfmisc_1(u1_struct_0(A_721)))
      | ~ l1_pre_topc(A_721)
      | ~ v2_pre_topc(A_721)
      | v2_struct_0(A_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8301,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_8299])).

tff(c_8304,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_8301])).

tff(c_8305,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8304])).

tff(c_46,plain,(
    ! [C_31,A_27,D_32,B_28] :
      ( C_31 = A_27
      | g1_pre_topc(C_31,D_32) != g1_pre_topc(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_8322,plain,(
    ! [A_723,B_724] :
      ( u1_struct_0('#skF_2') = A_723
      | k6_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_723,B_724)
      | ~ m1_subset_1(B_724,k1_zfmisc_1(k1_zfmisc_1(A_723))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8305,c_46])).

tff(c_8327,plain,(
    ! [A_725] :
      ( u1_struct_0(A_725) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_725),u1_pre_topc(A_725)) != k6_tmap_1('#skF_2','#skF_3')
      | ~ l1_pre_topc(A_725) ) ),
    inference(resolution,[status(thm)],[c_36,c_8322])).

tff(c_8337,plain,(
    ! [A_728] :
      ( u1_struct_0(A_728) = u1_struct_0('#skF_2')
      | k6_tmap_1('#skF_2','#skF_3') != A_728
      | ~ l1_pre_topc(A_728)
      | ~ v1_pre_topc(A_728)
      | ~ l1_pre_topc(A_728) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8327])).

tff(c_8340,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1579,c_8337])).

tff(c_8343,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_8340])).

tff(c_8452,plain,(
    ! [A_731,B_732] :
      ( v1_funct_2(k7_tmap_1(A_731,B_732),u1_struct_0(A_731),u1_struct_0(k6_tmap_1(A_731,B_732)))
      | ~ m1_subset_1(B_732,k1_zfmisc_1(u1_struct_0(A_731)))
      | ~ l1_pre_topc(A_731)
      | ~ v2_pre_topc(A_731)
      | v2_struct_0(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8458,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8343,c_8452])).

tff(c_8463,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_8458])).

tff(c_8464,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8463])).

tff(c_8281,plain,(
    ! [A_719,B_720] :
      ( k7_tmap_1(A_719,B_720) = k6_partfun1(u1_struct_0(A_719))
      | ~ m1_subset_1(B_720,k1_zfmisc_1(u1_struct_0(A_719)))
      | ~ l1_pre_topc(A_719)
      | ~ v2_pre_topc(A_719)
      | v2_struct_0(A_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8284,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_8281])).

tff(c_8287,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_8284])).

tff(c_8288,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8287])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8292,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8288,c_18])).

tff(c_8568,plain,(
    ! [A_745,B_746,C_747,D_748] :
      ( v1_funct_1(k2_tmap_1(A_745,B_746,C_747,D_748))
      | ~ l1_struct_0(D_748)
      | ~ m1_subset_1(C_747,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_745),u1_struct_0(B_746))))
      | ~ v1_funct_2(C_747,u1_struct_0(A_745),u1_struct_0(B_746))
      | ~ v1_funct_1(C_747)
      | ~ l1_struct_0(B_746)
      | ~ l1_struct_0(A_745) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8576,plain,(
    ! [D_748] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_748))
      | ~ l1_struct_0(D_748)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8292,c_8568])).

tff(c_8585,plain,(
    ! [D_748] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_748))
      | ~ l1_struct_0(D_748)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_8464,c_8576])).

tff(c_8587,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8585])).

tff(c_8590,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_8587])).

tff(c_8594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8590])).

tff(c_8596,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_8585])).

tff(c_8653,plain,(
    ! [A_752,B_753,C_754,D_755] :
      ( v1_funct_2(k2_tmap_1(A_752,B_753,C_754,D_755),u1_struct_0(D_755),u1_struct_0(B_753))
      | ~ l1_struct_0(D_755)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_752),u1_struct_0(B_753))))
      | ~ v1_funct_2(C_754,u1_struct_0(A_752),u1_struct_0(B_753))
      | ~ v1_funct_1(C_754)
      | ~ l1_struct_0(B_753)
      | ~ l1_struct_0(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8665,plain,(
    ! [D_755] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_755),u1_struct_0(D_755),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_755)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8292,c_8653])).

tff(c_8682,plain,(
    ! [D_756] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_756),u1_struct_0(D_756),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_756) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8596,c_1587,c_8464,c_8665])).

tff(c_8685,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8343,c_8682])).

tff(c_8778,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8685])).

tff(c_8781,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_8778])).

tff(c_8785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_8781])).

tff(c_8787,plain,(
    l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8685])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k7_tmap_1(A_18,B_19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_18),u1_struct_0(k6_tmap_1(A_18,B_19)))))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_9682,plain,(
    ! [A_840,B_841,D_842] :
      ( v1_funct_2(k2_tmap_1(A_840,k6_tmap_1(A_840,B_841),k7_tmap_1(A_840,B_841),D_842),u1_struct_0(D_842),u1_struct_0(k6_tmap_1(A_840,B_841)))
      | ~ l1_struct_0(D_842)
      | ~ v1_funct_2(k7_tmap_1(A_840,B_841),u1_struct_0(A_840),u1_struct_0(k6_tmap_1(A_840,B_841)))
      | ~ v1_funct_1(k7_tmap_1(A_840,B_841))
      | ~ l1_struct_0(k6_tmap_1(A_840,B_841))
      | ~ l1_struct_0(A_840)
      | ~ m1_subset_1(B_841,k1_zfmisc_1(u1_struct_0(A_840)))
      | ~ l1_pre_topc(A_840)
      | ~ v2_pre_topc(A_840)
      | v2_struct_0(A_840) ) ),
    inference(resolution,[status(thm)],[c_26,c_8653])).

tff(c_9694,plain,(
    ! [D_842] :
      ( v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_842),u1_struct_0(D_842),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_842)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8343,c_9682])).

tff(c_9701,plain,(
    ! [D_842] :
      ( v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_842),u1_struct_0(D_842),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_842)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_8596,c_8787,c_1587,c_8464,c_8343,c_9694])).

tff(c_9703,plain,(
    ! [D_843] :
      ( v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_843),u1_struct_0(D_843),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_843) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_9701])).

tff(c_1648,plain,(
    ! [A_265,B_266] :
      ( g1_pre_topc(u1_struct_0(A_265),k5_tmap_1(A_265,B_266)) = k6_tmap_1(A_265,B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1650,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1648])).

tff(c_1653,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1650])).

tff(c_1654,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1653])).

tff(c_1675,plain,(
    ! [A_267,B_268] :
      ( u1_struct_0('#skF_2') = A_267
      | k6_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_267,B_268)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(k1_zfmisc_1(A_267))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1654,c_46])).

tff(c_1680,plain,(
    ! [A_269] :
      ( u1_struct_0(A_269) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_269),u1_pre_topc(A_269)) != k6_tmap_1('#skF_2','#skF_3')
      | ~ l1_pre_topc(A_269) ) ),
    inference(resolution,[status(thm)],[c_36,c_1675])).

tff(c_1685,plain,(
    ! [A_270] :
      ( u1_struct_0(A_270) = u1_struct_0('#skF_2')
      | k6_tmap_1('#skF_2','#skF_3') != A_270
      | ~ l1_pre_topc(A_270)
      | ~ v1_pre_topc(A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1680])).

tff(c_1688,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1579,c_1685])).

tff(c_1691,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_1688])).

tff(c_1753,plain,(
    ! [A_271,B_272] :
      ( v1_funct_2(k7_tmap_1(A_271,B_272),u1_struct_0(A_271),u1_struct_0(k6_tmap_1(A_271,B_272)))
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1759,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1691,c_1753])).

tff(c_1764,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1759])).

tff(c_1765,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1764])).

tff(c_1607,plain,(
    ! [A_255,B_256] :
      ( k7_tmap_1(A_255,B_256) = k6_partfun1(u1_struct_0(A_255))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1610,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1607])).

tff(c_1613,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1610])).

tff(c_1614,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1613])).

tff(c_1618,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1614,c_18])).

tff(c_1894,plain,(
    ! [A_284,B_285,C_286,D_287] :
      ( v1_funct_1(k2_tmap_1(A_284,B_285,C_286,D_287))
      | ~ l1_struct_0(D_287)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_284),u1_struct_0(B_285))))
      | ~ v1_funct_2(C_286,u1_struct_0(A_284),u1_struct_0(B_285))
      | ~ v1_funct_1(C_286)
      | ~ l1_struct_0(B_285)
      | ~ l1_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1902,plain,(
    ! [D_287] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_287))
      | ~ l1_struct_0(D_287)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1618,c_1894])).

tff(c_1911,plain,(
    ! [D_287] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_287))
      | ~ l1_struct_0(D_287)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1765,c_1902])).

tff(c_1922,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1911])).

tff(c_1925,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1922])).

tff(c_1929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1925])).

tff(c_1931,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1911])).

tff(c_1970,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( v1_funct_2(k2_tmap_1(A_293,B_294,C_295,D_296),u1_struct_0(D_296),u1_struct_0(B_294))
      | ~ l1_struct_0(D_296)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293),u1_struct_0(B_294))))
      | ~ v1_funct_2(C_295,u1_struct_0(A_293),u1_struct_0(B_294))
      | ~ v1_funct_1(C_295)
      | ~ l1_struct_0(B_294)
      | ~ l1_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1978,plain,(
    ! [D_296] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_296),u1_struct_0(D_296),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_296)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1618,c_1970])).

tff(c_2003,plain,(
    ! [D_298] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_298),u1_struct_0(D_298),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1931,c_1587,c_1765,c_1978])).

tff(c_2006,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1691,c_2003])).

tff(c_2082,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2006])).

tff(c_2085,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_2082])).

tff(c_2089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_2085])).

tff(c_2091,plain,(
    l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2006])).

tff(c_2020,plain,(
    ! [A_299,B_300,C_301,D_302] :
      ( m1_subset_1(k2_tmap_1(A_299,B_300,C_301,D_302),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_302),u1_struct_0(B_300))))
      | ~ l1_struct_0(D_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_299),u1_struct_0(B_300))))
      | ~ v1_funct_2(C_301,u1_struct_0(A_299),u1_struct_0(B_300))
      | ~ v1_funct_1(C_301)
      | ~ l1_struct_0(B_300)
      | ~ l1_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2030,plain,(
    ! [A_299,C_301,D_302] :
      ( m1_subset_1(k2_tmap_1(A_299,k6_tmap_1('#skF_2','#skF_3'),C_301,D_302),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_302),u1_struct_0('#skF_2'))))
      | ~ l1_struct_0(D_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_299),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
      | ~ v1_funct_2(C_301,u1_struct_0(A_299),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_301)
      | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0(A_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1691,c_2020])).

tff(c_2033,plain,(
    ! [A_299,C_301,D_302] :
      ( m1_subset_1(k2_tmap_1(A_299,k6_tmap_1('#skF_2','#skF_3'),C_301,D_302),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_302),u1_struct_0('#skF_2'))))
      | ~ l1_struct_0(D_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_299),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_301,u1_struct_0(A_299),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_301)
      | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0(A_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_1691,c_2030])).

tff(c_8139,plain,(
    ! [A_713,C_714,D_715] :
      ( m1_subset_1(k2_tmap_1(A_713,k6_tmap_1('#skF_2','#skF_3'),C_714,D_715),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_715),u1_struct_0('#skF_2'))))
      | ~ l1_struct_0(D_715)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_713),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_714,u1_struct_0(A_713),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_714)
      | ~ l1_struct_0(A_713) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2091,c_2033])).

tff(c_74,plain,(
    ! [B_76,A_77] :
      ( l1_pre_topc(B_76)
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_74])).

tff(c_80,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_77])).

tff(c_125,plain,(
    ! [A_93,B_94] :
      ( v1_funct_1(k7_tmap_1(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_128,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_125])).

tff(c_131,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_128])).

tff(c_132,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_131])).

tff(c_133,plain,(
    ! [A_95,B_96] :
      ( l1_pre_topc(k6_tmap_1(A_95,B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_136,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_133])).

tff(c_139,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_136])).

tff(c_140,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_139])).

tff(c_149,plain,(
    ! [A_99,B_100] :
      ( v1_pre_topc(k6_tmap_1(A_99,B_100))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_152,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_149])).

tff(c_155,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_152])).

tff(c_156,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_155])).

tff(c_193,plain,(
    ! [A_109,B_110] :
      ( g1_pre_topc(u1_struct_0(A_109),k5_tmap_1(A_109,B_110)) = k6_tmap_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_195,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_193])).

tff(c_198,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_195])).

tff(c_199,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_198])).

tff(c_216,plain,(
    ! [A_111,B_112] :
      ( u1_struct_0('#skF_2') = A_111
      | k6_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_111,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_46])).

tff(c_226,plain,(
    ! [A_115] :
      ( u1_struct_0(A_115) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_115),u1_pre_topc(A_115)) != k6_tmap_1('#skF_2','#skF_3')
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_36,c_216])).

tff(c_231,plain,(
    ! [A_116] :
      ( u1_struct_0(A_116) = u1_struct_0('#skF_2')
      | k6_tmap_1('#skF_2','#skF_3') != A_116
      | ~ l1_pre_topc(A_116)
      | ~ v1_pre_topc(A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_226])).

tff(c_234,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_156,c_231])).

tff(c_237,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_234])).

tff(c_331,plain,(
    ! [A_117,B_118] :
      ( v1_funct_2(k7_tmap_1(A_117,B_118),u1_struct_0(A_117),u1_struct_0(k6_tmap_1(A_117,B_118)))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_337,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_331])).

tff(c_342,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_337])).

tff(c_343,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_342])).

tff(c_175,plain,(
    ! [A_107,B_108] :
      ( k7_tmap_1(A_107,B_108) = k6_partfun1(u1_struct_0(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_175])).

tff(c_181,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_178])).

tff(c_182,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_181])).

tff(c_186,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_18])).

tff(c_461,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( v1_funct_1(k2_tmap_1(A_131,B_132,C_133,D_134))
      | ~ l1_struct_0(D_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(B_132))))
      | ~ v1_funct_2(C_133,u1_struct_0(A_131),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ l1_struct_0(B_132)
      | ~ l1_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_469,plain,(
    ! [D_134] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_134))
      | ~ l1_struct_0(D_134)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_186,c_461])).

tff(c_478,plain,(
    ! [D_134] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_134))
      | ~ l1_struct_0(D_134)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_343,c_469])).

tff(c_489,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_492,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_489])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_492])).

tff(c_498,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_528,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( v1_funct_2(k2_tmap_1(A_140,B_141,C_142,D_143),u1_struct_0(D_143),u1_struct_0(B_141))
      | ~ l1_struct_0(D_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140),u1_struct_0(B_141))))
      | ~ v1_funct_2(C_142,u1_struct_0(A_140),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ l1_struct_0(B_141)
      | ~ l1_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_536,plain,(
    ! [D_143] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_143),u1_struct_0(D_143),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_143)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_186,c_528])).

tff(c_547,plain,(
    ! [D_144] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_144),u1_struct_0(D_144),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_132,c_343,c_536])).

tff(c_550,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_547])).

tff(c_668,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_671,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_668])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_671])).

tff(c_677,plain,(
    l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_1470,plain,(
    ! [A_220,B_221,D_222] :
      ( v1_funct_1(k2_tmap_1(A_220,k6_tmap_1(A_220,B_221),k7_tmap_1(A_220,B_221),D_222))
      | ~ l1_struct_0(D_222)
      | ~ v1_funct_2(k7_tmap_1(A_220,B_221),u1_struct_0(A_220),u1_struct_0(k6_tmap_1(A_220,B_221)))
      | ~ v1_funct_1(k7_tmap_1(A_220,B_221))
      | ~ l1_struct_0(k6_tmap_1(A_220,B_221))
      | ~ l1_struct_0(A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_26,c_461])).

tff(c_1480,plain,(
    ! [D_222] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_222))
      | ~ l1_struct_0(D_222)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_1470])).

tff(c_1489,plain,(
    ! [D_222] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_222))
      | ~ l1_struct_0(D_222)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_498,c_677,c_132,c_343,c_1480])).

tff(c_1491,plain,(
    ! [D_223] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_223))
      | ~ l1_struct_0(D_223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1489])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_73,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1495,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1491,c_73])).

tff(c_1498,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1495])).

tff(c_1502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1498])).

tff(c_1503,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1597,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_1503])).

tff(c_1692,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_1597])).

tff(c_8183,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8139,c_1692])).

tff(c_8253,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1931,c_1587,c_1765,c_1618,c_8183])).

tff(c_8266,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_8253])).

tff(c_8270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_8266])).

tff(c_8271,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1503])).

tff(c_8636,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8343,c_8271])).

tff(c_8637,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8636])).

tff(c_9713,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_9703,c_8637])).

tff(c_9718,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_9713])).

tff(c_9722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_9718])).

tff(c_9723,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8636])).

tff(c_58,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_1514,plain,(
    ! [B_228,A_229] :
      ( v2_pre_topc(B_228)
      | ~ m1_pre_topc(B_228,A_229)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1517,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1514])).

tff(c_1520,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1517])).

tff(c_1504,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_9724,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_8636])).

tff(c_8272,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_1503])).

tff(c_8344,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8343,c_8272])).

tff(c_1548,plain,(
    ! [A_239,B_240] :
      ( ~ v2_struct_0(k6_tmap_1(A_239,B_240))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1551,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1548])).

tff(c_1554,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1551])).

tff(c_1555,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1554])).

tff(c_1556,plain,(
    ! [A_241,B_242] :
      ( v2_pre_topc(k6_tmap_1(A_241,B_242))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1559,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1556])).

tff(c_1562,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1559])).

tff(c_1563,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1562])).

tff(c_9944,plain,(
    ! [A_870,B_871,C_872] :
      ( m1_subset_1('#skF_1'(A_870,B_871,C_872),u1_struct_0(B_871))
      | v5_pre_topc(C_872,B_871,A_870)
      | ~ m1_subset_1(C_872,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_871),u1_struct_0(A_870))))
      | ~ v1_funct_2(C_872,u1_struct_0(B_871),u1_struct_0(A_870))
      | ~ v1_funct_1(C_872)
      | ~ l1_pre_topc(B_871)
      | ~ v2_pre_topc(B_871)
      | v2_struct_0(B_871)
      | ~ l1_pre_topc(A_870)
      | ~ v2_pre_topc(A_870)
      | v2_struct_0(A_870) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_9956,plain,(
    ! [B_871,C_872] :
      ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),B_871,C_872),u1_struct_0(B_871))
      | v5_pre_topc(C_872,B_871,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_872,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_871),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_872,u1_struct_0(B_871),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_872)
      | ~ l1_pre_topc(B_871)
      | ~ v2_pre_topc(B_871)
      | v2_struct_0(B_871)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8343,c_9944])).

tff(c_9976,plain,(
    ! [B_871,C_872] :
      ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),B_871,C_872),u1_struct_0(B_871))
      | v5_pre_topc(C_872,B_871,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_872,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_871),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_872,u1_struct_0(B_871),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_872)
      | ~ l1_pre_topc(B_871)
      | ~ v2_pre_topc(B_871)
      | v2_struct_0(B_871)
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_1571,c_8343,c_9956])).

tff(c_10648,plain,(
    ! [B_925,C_926] :
      ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),B_925,C_926),u1_struct_0(B_925))
      | v5_pre_topc(C_926,B_925,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_926,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_925),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_926,u1_struct_0(B_925),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_926)
      | ~ l1_pre_topc(B_925)
      | ~ v2_pre_topc(B_925)
      | v2_struct_0(B_925) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1555,c_9976])).

tff(c_10655,plain,
    ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8344,c_10648])).

tff(c_10668,plain,
    ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_1511,c_1504,c_9724,c_10655])).

tff(c_10669,plain,(
    m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_9723,c_10668])).

tff(c_48,plain,(
    ! [C_45,A_33,B_41,D_47] :
      ( r1_tmap_1(C_45,k6_tmap_1(A_33,B_41),k2_tmap_1(A_33,k6_tmap_1(A_33,B_41),k7_tmap_1(A_33,B_41),C_45),D_47)
      | ~ m1_subset_1(D_47,u1_struct_0(C_45))
      | ~ r1_xboole_0(u1_struct_0(C_45),B_41)
      | ~ m1_pre_topc(C_45,A_33)
      | v2_struct_0(C_45)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_10247,plain,(
    ! [B_889,A_890,C_891] :
      ( ~ r1_tmap_1(B_889,A_890,C_891,'#skF_1'(A_890,B_889,C_891))
      | v5_pre_topc(C_891,B_889,A_890)
      | ~ m1_subset_1(C_891,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_889),u1_struct_0(A_890))))
      | ~ v1_funct_2(C_891,u1_struct_0(B_889),u1_struct_0(A_890))
      | ~ v1_funct_1(C_891)
      | ~ l1_pre_topc(B_889)
      | ~ v2_pre_topc(B_889)
      | v2_struct_0(B_889)
      | ~ l1_pre_topc(A_890)
      | ~ v2_pre_topc(A_890)
      | v2_struct_0(A_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_12130,plain,(
    ! [A_1012,B_1013,C_1014] :
      ( v5_pre_topc(k2_tmap_1(A_1012,k6_tmap_1(A_1012,B_1013),k7_tmap_1(A_1012,B_1013),C_1014),C_1014,k6_tmap_1(A_1012,B_1013))
      | ~ m1_subset_1(k2_tmap_1(A_1012,k6_tmap_1(A_1012,B_1013),k7_tmap_1(A_1012,B_1013),C_1014),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1014),u1_struct_0(k6_tmap_1(A_1012,B_1013)))))
      | ~ v1_funct_2(k2_tmap_1(A_1012,k6_tmap_1(A_1012,B_1013),k7_tmap_1(A_1012,B_1013),C_1014),u1_struct_0(C_1014),u1_struct_0(k6_tmap_1(A_1012,B_1013)))
      | ~ v1_funct_1(k2_tmap_1(A_1012,k6_tmap_1(A_1012,B_1013),k7_tmap_1(A_1012,B_1013),C_1014))
      | ~ l1_pre_topc(C_1014)
      | ~ v2_pre_topc(C_1014)
      | ~ l1_pre_topc(k6_tmap_1(A_1012,B_1013))
      | ~ v2_pre_topc(k6_tmap_1(A_1012,B_1013))
      | v2_struct_0(k6_tmap_1(A_1012,B_1013))
      | ~ m1_subset_1('#skF_1'(k6_tmap_1(A_1012,B_1013),C_1014,k2_tmap_1(A_1012,k6_tmap_1(A_1012,B_1013),k7_tmap_1(A_1012,B_1013),C_1014)),u1_struct_0(C_1014))
      | ~ r1_xboole_0(u1_struct_0(C_1014),B_1013)
      | ~ m1_pre_topc(C_1014,A_1012)
      | v2_struct_0(C_1014)
      | ~ m1_subset_1(B_1013,k1_zfmisc_1(u1_struct_0(A_1012)))
      | ~ l1_pre_topc(A_1012)
      | ~ v2_pre_topc(A_1012)
      | v2_struct_0(A_1012) ) ),
    inference(resolution,[status(thm)],[c_48,c_10247])).

tff(c_12149,plain,(
    ! [C_1014] :
      ( v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014),C_1014,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1014),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014),u1_struct_0(C_1014),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014))
      | ~ l1_pre_topc(C_1014)
      | ~ v2_pre_topc(C_1014)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),C_1014,k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014)),u1_struct_0(C_1014))
      | ~ r1_xboole_0(u1_struct_0(C_1014),'#skF_3')
      | ~ m1_pre_topc(C_1014,'#skF_2')
      | v2_struct_0(C_1014)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8343,c_12130])).

tff(c_12167,plain,(
    ! [C_1014] :
      ( v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014),C_1014,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1014),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014),u1_struct_0(C_1014),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014))
      | ~ l1_pre_topc(C_1014)
      | ~ v2_pre_topc(C_1014)
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),C_1014,k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1014)),u1_struct_0(C_1014))
      | ~ r1_xboole_0(u1_struct_0(C_1014),'#skF_3')
      | ~ m1_pre_topc(C_1014,'#skF_2')
      | v2_struct_0(C_1014)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1563,c_1571,c_8343,c_12149])).

tff(c_12618,plain,(
    ! [C_1050] :
      ( v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1050),C_1050,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1050),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1050),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1050),u1_struct_0(C_1050),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1050))
      | ~ l1_pre_topc(C_1050)
      | ~ v2_pre_topc(C_1050)
      | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),C_1050,k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),C_1050)),u1_struct_0(C_1050))
      | ~ r1_xboole_0(u1_struct_0(C_1050),'#skF_3')
      | ~ m1_pre_topc(C_1050,'#skF_2')
      | v2_struct_0(C_1050) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1555,c_12167])).

tff(c_12626,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | ~ r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8344,c_12618])).

tff(c_12634,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_10669,c_1520,c_1511,c_1504,c_9724,c_12626])).

tff(c_12636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_9723,c_12634])).

%------------------------------------------------------------------------------
