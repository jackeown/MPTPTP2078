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
% DateTime   : Thu Dec  3 10:27:44 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 412 expanded)
%              Number of leaves         :   37 ( 169 expanded)
%              Depth                    :   13
%              Number of atoms          :  494 (2964 expanded)
%              Number of equality atoms :   53 (  78 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_231,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_165,axiom,(
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

tff(f_132,axiom,(
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
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_172,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_90,plain,(
    ! [B_103,A_104] :
      ( v2_pre_topc(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_99,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_90])).

tff(c_108,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_99])).

tff(c_70,plain,(
    ! [B_100,A_101] :
      ( l1_pre_topc(B_100)
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_79,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_70])).

tff(c_86,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_79])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_44,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1400,plain,(
    ! [A_356,B_357,C_358,D_359] :
      ( v5_pre_topc(k2_tmap_1(A_356,B_357,C_358,D_359),D_359,B_357)
      | ~ m1_pre_topc(D_359,A_356)
      | v2_struct_0(D_359)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356),u1_struct_0(B_357))))
      | ~ v5_pre_topc(C_358,A_356,B_357)
      | ~ v1_funct_2(C_358,u1_struct_0(A_356),u1_struct_0(B_357))
      | ~ v1_funct_1(C_358)
      | ~ l1_pre_topc(B_357)
      | ~ v2_pre_topc(B_357)
      | v2_struct_0(B_357)
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1410,plain,(
    ! [D_359] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_359),D_359,'#skF_2')
      | ~ m1_pre_topc(D_359,'#skF_3')
      | v2_struct_0(D_359)
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_1400])).

tff(c_1419,plain,(
    ! [D_359] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_359),D_359,'#skF_2')
      | ~ m1_pre_topc(D_359,'#skF_3')
      | v2_struct_0(D_359)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_86,c_60,c_58,c_48,c_46,c_44,c_1410])).

tff(c_1420,plain,(
    ! [D_359] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_359),D_359,'#skF_2')
      | ~ m1_pre_topc(D_359,'#skF_3')
      | v2_struct_0(D_359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_1419])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1611,plain,(
    ! [D_396,E_392,B_395,C_394,A_393] :
      ( k3_tmap_1(A_393,B_395,C_394,D_396,E_392) = k2_partfun1(u1_struct_0(C_394),u1_struct_0(B_395),E_392,u1_struct_0(D_396))
      | ~ m1_pre_topc(D_396,C_394)
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394),u1_struct_0(B_395))))
      | ~ v1_funct_2(E_392,u1_struct_0(C_394),u1_struct_0(B_395))
      | ~ v1_funct_1(E_392)
      | ~ m1_pre_topc(D_396,A_393)
      | ~ m1_pre_topc(C_394,A_393)
      | ~ l1_pre_topc(B_395)
      | ~ v2_pre_topc(B_395)
      | v2_struct_0(B_395)
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1625,plain,(
    ! [A_393,D_396] :
      ( k3_tmap_1(A_393,'#skF_2','#skF_3',D_396,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_396))
      | ~ m1_pre_topc(D_396,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_396,A_393)
      | ~ m1_pre_topc('#skF_3',A_393)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(resolution,[status(thm)],[c_42,c_1611])).

tff(c_1642,plain,(
    ! [A_393,D_396] :
      ( k3_tmap_1(A_393,'#skF_2','#skF_3',D_396,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_396))
      | ~ m1_pre_topc(D_396,'#skF_3')
      | ~ m1_pre_topc(D_396,A_393)
      | ~ m1_pre_topc('#skF_3',A_393)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_1625])).

tff(c_1644,plain,(
    ! [A_397,D_398] :
      ( k3_tmap_1(A_397,'#skF_2','#skF_3',D_398,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_398))
      | ~ m1_pre_topc(D_398,'#skF_3')
      | ~ m1_pre_topc(D_398,A_397)
      | ~ m1_pre_topc('#skF_3',A_397)
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1642])).

tff(c_1648,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1644])).

tff(c_1656,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_40,c_1648])).

tff(c_1657,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1656])).

tff(c_1318,plain,(
    ! [A_345,B_346,C_347,D_348] :
      ( k2_partfun1(u1_struct_0(A_345),u1_struct_0(B_346),C_347,u1_struct_0(D_348)) = k2_tmap_1(A_345,B_346,C_347,D_348)
      | ~ m1_pre_topc(D_348,A_345)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345),u1_struct_0(B_346))))
      | ~ v1_funct_2(C_347,u1_struct_0(A_345),u1_struct_0(B_346))
      | ~ v1_funct_1(C_347)
      | ~ l1_pre_topc(B_346)
      | ~ v2_pre_topc(B_346)
      | v2_struct_0(B_346)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1328,plain,(
    ! [D_348] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_348)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_348)
      | ~ m1_pre_topc(D_348,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_1318])).

tff(c_1337,plain,(
    ! [D_348] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_348)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_348)
      | ~ m1_pre_topc(D_348,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_86,c_60,c_58,c_48,c_46,c_1328])).

tff(c_1338,plain,(
    ! [D_348] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_348)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_348)
      | ~ m1_pre_topc(D_348,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_1337])).

tff(c_1672,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_1338])).

tff(c_1690,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1672])).

tff(c_34,plain,(
    ! [B_65,A_63] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0(A_63))
      | ~ m1_pre_topc(B_65,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_38,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_123,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_445,plain,(
    ! [A_188,B_190,C_189,E_187,D_191] :
      ( k3_tmap_1(A_188,B_190,C_189,D_191,E_187) = k2_partfun1(u1_struct_0(C_189),u1_struct_0(B_190),E_187,u1_struct_0(D_191))
      | ~ m1_pre_topc(D_191,C_189)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_189),u1_struct_0(B_190))))
      | ~ v1_funct_2(E_187,u1_struct_0(C_189),u1_struct_0(B_190))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc(D_191,A_188)
      | ~ m1_pre_topc(C_189,A_188)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_455,plain,(
    ! [A_188,D_191] :
      ( k3_tmap_1(A_188,'#skF_2','#skF_3',D_191,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_191))
      | ~ m1_pre_topc(D_191,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_191,A_188)
      | ~ m1_pre_topc('#skF_3',A_188)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_42,c_445])).

tff(c_464,plain,(
    ! [A_188,D_191] :
      ( k3_tmap_1(A_188,'#skF_2','#skF_3',D_191,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_191))
      | ~ m1_pre_topc(D_191,'#skF_3')
      | ~ m1_pre_topc(D_191,A_188)
      | ~ m1_pre_topc('#skF_3',A_188)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_455])).

tff(c_466,plain,(
    ! [A_192,D_193] :
      ( k3_tmap_1(A_192,'#skF_2','#skF_3',D_193,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_193))
      | ~ m1_pre_topc(D_193,'#skF_3')
      | ~ m1_pre_topc(D_193,A_192)
      | ~ m1_pre_topc('#skF_3',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_464])).

tff(c_470,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_466])).

tff(c_478,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_40,c_470])).

tff(c_479,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_478])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_173,plain,(
    ! [B_121,A_122,D_123,C_124] :
      ( k1_xboole_0 = B_121
      | v1_funct_1(k2_partfun1(A_122,B_121,D_123,C_124))
      | ~ r1_tarski(C_124,A_122)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2(D_123,A_122,B_121)
      | ~ v1_funct_1(D_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_175,plain,(
    ! [C_124] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_124))
      | ~ r1_tarski(C_124,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_178,plain,(
    ! [C_124] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_124))
      | ~ r1_tarski(C_124,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_175])).

tff(c_179,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_22,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_191,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_22])).

tff(c_197,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_198,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_197])).

tff(c_202,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_198])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_202])).

tff(c_207,plain,(
    ! [C_124] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_124))
      | ~ r1_tarski(C_124,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_503,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_207])).

tff(c_515,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_503])).

tff(c_521,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_515])).

tff(c_525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_40,c_521])).

tff(c_526,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_653,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_577,plain,(
    ! [B_204,A_205,D_206,C_207] :
      ( k1_xboole_0 = B_204
      | v1_funct_1(k2_partfun1(A_205,B_204,D_206,C_207))
      | ~ r1_tarski(C_207,A_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204)))
      | ~ v1_funct_2(D_206,A_205,B_204)
      | ~ v1_funct_1(D_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_579,plain,(
    ! [C_207] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_207))
      | ~ r1_tarski(C_207,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_577])).

tff(c_582,plain,(
    ! [C_207] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_207))
      | ~ r1_tarski(C_207,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_579])).

tff(c_583,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_582])).

tff(c_596,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_22])).

tff(c_602,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_596])).

tff(c_603,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_602])).

tff(c_607,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_603])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_607])).

tff(c_613,plain,(
    u1_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_823,plain,(
    ! [A_263,E_262,C_264,D_266,B_265] :
      ( k3_tmap_1(A_263,B_265,C_264,D_266,E_262) = k2_partfun1(u1_struct_0(C_264),u1_struct_0(B_265),E_262,u1_struct_0(D_266))
      | ~ m1_pre_topc(D_266,C_264)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_264),u1_struct_0(B_265))))
      | ~ v1_funct_2(E_262,u1_struct_0(C_264),u1_struct_0(B_265))
      | ~ v1_funct_1(E_262)
      | ~ m1_pre_topc(D_266,A_263)
      | ~ m1_pre_topc(C_264,A_263)
      | ~ l1_pre_topc(B_265)
      | ~ v2_pre_topc(B_265)
      | v2_struct_0(B_265)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_833,plain,(
    ! [A_263,D_266] :
      ( k3_tmap_1(A_263,'#skF_2','#skF_3',D_266,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_266))
      | ~ m1_pre_topc(D_266,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_266,A_263)
      | ~ m1_pre_topc('#skF_3',A_263)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(resolution,[status(thm)],[c_42,c_823])).

tff(c_842,plain,(
    ! [A_263,D_266] :
      ( k3_tmap_1(A_263,'#skF_2','#skF_3',D_266,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_266))
      | ~ m1_pre_topc(D_266,'#skF_3')
      | ~ m1_pre_topc(D_266,A_263)
      | ~ m1_pre_topc('#skF_3',A_263)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_833])).

tff(c_844,plain,(
    ! [A_267,D_268] :
      ( k3_tmap_1(A_267,'#skF_2','#skF_3',D_268,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_268))
      | ~ m1_pre_topc(D_268,'#skF_3')
      | ~ m1_pre_topc(D_268,A_267)
      | ~ m1_pre_topc('#skF_3',A_267)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_842])).

tff(c_848,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_844])).

tff(c_856,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_40,c_848])).

tff(c_857,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_856])).

tff(c_6,plain,(
    ! [B_2,A_1,D_4,C_3] :
      ( k1_xboole_0 = B_2
      | m1_subset_1(k2_partfun1(A_1,B_2,D_4,C_3),k1_zfmisc_1(k2_zfmisc_1(C_3,B_2)))
      | ~ r1_tarski(C_3,A_1)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_875,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_6])).

tff(c_892,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_875])).

tff(c_893,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_653,c_613,c_892])).

tff(c_900,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_893])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_40,c_900])).

tff(c_905,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_919,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_905])).

tff(c_1188,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1200,plain,(
    ! [A_332,D_335] :
      ( k3_tmap_1(A_332,'#skF_2','#skF_3',D_335,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_335,A_332)
      | ~ m1_pre_topc('#skF_3',A_332)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(resolution,[status(thm)],[c_42,c_1188])).

tff(c_1213,plain,(
    ! [A_332,D_335] :
      ( k3_tmap_1(A_332,'#skF_2','#skF_3',D_335,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,'#skF_3')
      | ~ m1_pre_topc(D_335,A_332)
      | ~ m1_pre_topc('#skF_3',A_332)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_1200])).

tff(c_1215,plain,(
    ! [A_336,D_337] :
      ( k3_tmap_1(A_336,'#skF_2','#skF_3',D_337,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_337))
      | ~ m1_pre_topc(D_337,'#skF_3')
      | ~ m1_pre_topc(D_337,A_336)
      | ~ m1_pre_topc('#skF_3',A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1213])).

tff(c_1219,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1215])).

tff(c_1227,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_40,c_1219])).

tff(c_1228,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1227])).

tff(c_615,plain,(
    ! [B_209,A_210,D_211,C_212] :
      ( k1_xboole_0 = B_209
      | v1_funct_2(k2_partfun1(A_210,B_209,D_211,C_212),C_212,B_209)
      | ~ r1_tarski(C_212,A_210)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209)))
      | ~ v1_funct_2(D_211,A_210,B_209)
      | ~ v1_funct_1(D_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_617,plain,(
    ! [C_212] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_212),C_212,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_212,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_615])).

tff(c_620,plain,(
    ! [C_212] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_212),C_212,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_212,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_617])).

tff(c_621,plain,(
    ! [C_212] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',C_212),C_212,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_212,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_620])).

tff(c_1254,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_621])).

tff(c_1275,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_919,c_1254])).

tff(c_1282,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1275])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_40,c_1282])).

tff(c_1287,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_905])).

tff(c_1707,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1287])).

tff(c_1723,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1420,c_1707])).

tff(c_1726,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1723])).

tff(c_1728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.05  
% 5.65/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.05  %$ v5_pre_topc > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.65/2.05  
% 5.65/2.05  %Foreground sorts:
% 5.65/2.05  
% 5.65/2.05  
% 5.65/2.05  %Background operators:
% 5.65/2.05  
% 5.65/2.05  
% 5.65/2.05  %Foreground operators:
% 5.65/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.65/2.05  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.65/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.65/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.65/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.65/2.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.65/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.65/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.65/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.65/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.65/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.65/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.65/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.65/2.05  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.65/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.65/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.65/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.65/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.65/2.05  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.65/2.05  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.65/2.05  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.65/2.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.65/2.05  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.65/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.65/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.65/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.65/2.05  
% 5.81/2.09  tff(f_231, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, C, D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_tmap_1)).
% 5.81/2.09  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.81/2.09  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.81/2.09  tff(f_165, axiom, (![A, B, C, D]: ((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tmap_1)).
% 5.81/2.09  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.81/2.09  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.81/2.09  tff(f_172, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 5.81/2.09  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.81/2.09  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.81/2.09  tff(f_45, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 5.81/2.09  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.81/2.09  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_90, plain, (![B_103, A_104]: (v2_pre_topc(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.81/2.09  tff(c_99, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_90])).
% 5.81/2.09  tff(c_108, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_99])).
% 5.81/2.09  tff(c_70, plain, (![B_100, A_101]: (l1_pre_topc(B_100) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.81/2.09  tff(c_79, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_70])).
% 5.81/2.09  tff(c_86, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_79])).
% 5.81/2.09  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_44, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_1400, plain, (![A_356, B_357, C_358, D_359]: (v5_pre_topc(k2_tmap_1(A_356, B_357, C_358, D_359), D_359, B_357) | ~m1_pre_topc(D_359, A_356) | v2_struct_0(D_359) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356), u1_struct_0(B_357)))) | ~v5_pre_topc(C_358, A_356, B_357) | ~v1_funct_2(C_358, u1_struct_0(A_356), u1_struct_0(B_357)) | ~v1_funct_1(C_358) | ~l1_pre_topc(B_357) | ~v2_pre_topc(B_357) | v2_struct_0(B_357) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356) | v2_struct_0(A_356))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.81/2.09  tff(c_1410, plain, (![D_359]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_359), D_359, '#skF_2') | ~m1_pre_topc(D_359, '#skF_3') | v2_struct_0(D_359) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_1400])).
% 5.81/2.09  tff(c_1419, plain, (![D_359]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_359), D_359, '#skF_2') | ~m1_pre_topc(D_359, '#skF_3') | v2_struct_0(D_359) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_86, c_60, c_58, c_48, c_46, c_44, c_1410])).
% 5.81/2.09  tff(c_1420, plain, (![D_359]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_359), D_359, '#skF_2') | ~m1_pre_topc(D_359, '#skF_3') | v2_struct_0(D_359))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_1419])).
% 5.81/2.09  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_1611, plain, (![D_396, E_392, B_395, C_394, A_393]: (k3_tmap_1(A_393, B_395, C_394, D_396, E_392)=k2_partfun1(u1_struct_0(C_394), u1_struct_0(B_395), E_392, u1_struct_0(D_396)) | ~m1_pre_topc(D_396, C_394) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394), u1_struct_0(B_395)))) | ~v1_funct_2(E_392, u1_struct_0(C_394), u1_struct_0(B_395)) | ~v1_funct_1(E_392) | ~m1_pre_topc(D_396, A_393) | ~m1_pre_topc(C_394, A_393) | ~l1_pre_topc(B_395) | ~v2_pre_topc(B_395) | v2_struct_0(B_395) | ~l1_pre_topc(A_393) | ~v2_pre_topc(A_393) | v2_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.81/2.09  tff(c_1625, plain, (![A_393, D_396]: (k3_tmap_1(A_393, '#skF_2', '#skF_3', D_396, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_396)) | ~m1_pre_topc(D_396, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_396, A_393) | ~m1_pre_topc('#skF_3', A_393) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_393) | ~v2_pre_topc(A_393) | v2_struct_0(A_393))), inference(resolution, [status(thm)], [c_42, c_1611])).
% 5.81/2.09  tff(c_1642, plain, (![A_393, D_396]: (k3_tmap_1(A_393, '#skF_2', '#skF_3', D_396, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_396)) | ~m1_pre_topc(D_396, '#skF_3') | ~m1_pre_topc(D_396, A_393) | ~m1_pre_topc('#skF_3', A_393) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_393) | ~v2_pre_topc(A_393) | v2_struct_0(A_393))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_1625])).
% 5.81/2.09  tff(c_1644, plain, (![A_397, D_398]: (k3_tmap_1(A_397, '#skF_2', '#skF_3', D_398, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_398)) | ~m1_pre_topc(D_398, '#skF_3') | ~m1_pre_topc(D_398, A_397) | ~m1_pre_topc('#skF_3', A_397) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(negUnitSimplification, [status(thm)], [c_62, c_1642])).
% 5.81/2.09  tff(c_1648, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1644])).
% 5.81/2.09  tff(c_1656, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_40, c_1648])).
% 5.81/2.09  tff(c_1657, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_1656])).
% 5.81/2.09  tff(c_1318, plain, (![A_345, B_346, C_347, D_348]: (k2_partfun1(u1_struct_0(A_345), u1_struct_0(B_346), C_347, u1_struct_0(D_348))=k2_tmap_1(A_345, B_346, C_347, D_348) | ~m1_pre_topc(D_348, A_345) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345), u1_struct_0(B_346)))) | ~v1_funct_2(C_347, u1_struct_0(A_345), u1_struct_0(B_346)) | ~v1_funct_1(C_347) | ~l1_pre_topc(B_346) | ~v2_pre_topc(B_346) | v2_struct_0(B_346) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.81/2.09  tff(c_1328, plain, (![D_348]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_348))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_348) | ~m1_pre_topc(D_348, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_1318])).
% 5.81/2.09  tff(c_1337, plain, (![D_348]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_348))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_348) | ~m1_pre_topc(D_348, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_86, c_60, c_58, c_48, c_46, c_1328])).
% 5.81/2.09  tff(c_1338, plain, (![D_348]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_348))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_348) | ~m1_pre_topc(D_348, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_1337])).
% 5.81/2.09  tff(c_1672, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1657, c_1338])).
% 5.81/2.09  tff(c_1690, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1672])).
% 5.81/2.09  tff(c_34, plain, (![B_65, A_63]: (r1_tarski(u1_struct_0(B_65), u1_struct_0(A_63)) | ~m1_pre_topc(B_65, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.81/2.09  tff(c_38, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.81/2.09  tff(c_123, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_38])).
% 5.81/2.09  tff(c_445, plain, (![A_188, B_190, C_189, E_187, D_191]: (k3_tmap_1(A_188, B_190, C_189, D_191, E_187)=k2_partfun1(u1_struct_0(C_189), u1_struct_0(B_190), E_187, u1_struct_0(D_191)) | ~m1_pre_topc(D_191, C_189) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_189), u1_struct_0(B_190)))) | ~v1_funct_2(E_187, u1_struct_0(C_189), u1_struct_0(B_190)) | ~v1_funct_1(E_187) | ~m1_pre_topc(D_191, A_188) | ~m1_pre_topc(C_189, A_188) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.81/2.09  tff(c_455, plain, (![A_188, D_191]: (k3_tmap_1(A_188, '#skF_2', '#skF_3', D_191, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_191)) | ~m1_pre_topc(D_191, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_191, A_188) | ~m1_pre_topc('#skF_3', A_188) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_42, c_445])).
% 5.81/2.09  tff(c_464, plain, (![A_188, D_191]: (k3_tmap_1(A_188, '#skF_2', '#skF_3', D_191, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_191)) | ~m1_pre_topc(D_191, '#skF_3') | ~m1_pre_topc(D_191, A_188) | ~m1_pre_topc('#skF_3', A_188) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_455])).
% 5.81/2.09  tff(c_466, plain, (![A_192, D_193]: (k3_tmap_1(A_192, '#skF_2', '#skF_3', D_193, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_193)) | ~m1_pre_topc(D_193, '#skF_3') | ~m1_pre_topc(D_193, A_192) | ~m1_pre_topc('#skF_3', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(negUnitSimplification, [status(thm)], [c_62, c_464])).
% 5.81/2.09  tff(c_470, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_466])).
% 5.81/2.09  tff(c_478, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_40, c_470])).
% 5.81/2.09  tff(c_479, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_478])).
% 5.81/2.09  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.81/2.09  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.81/2.09  tff(c_173, plain, (![B_121, A_122, D_123, C_124]: (k1_xboole_0=B_121 | v1_funct_1(k2_partfun1(A_122, B_121, D_123, C_124)) | ~r1_tarski(C_124, A_122) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2(D_123, A_122, B_121) | ~v1_funct_1(D_123))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.09  tff(c_175, plain, (![C_124]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_124)) | ~r1_tarski(C_124, u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_173])).
% 5.81/2.09  tff(c_178, plain, (![C_124]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_124)) | ~r1_tarski(C_124, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_175])).
% 5.81/2.09  tff(c_179, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_178])).
% 5.81/2.09  tff(c_22, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.81/2.09  tff(c_191, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_179, c_22])).
% 5.81/2.09  tff(c_197, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_191])).
% 5.81/2.09  tff(c_198, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_197])).
% 5.81/2.09  tff(c_202, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_198])).
% 5.81/2.09  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_202])).
% 5.81/2.09  tff(c_207, plain, (![C_124]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_124)) | ~r1_tarski(C_124, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_178])).
% 5.81/2.09  tff(c_503, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_479, c_207])).
% 5.81/2.09  tff(c_515, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_123, c_503])).
% 5.81/2.09  tff(c_521, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_515])).
% 5.81/2.09  tff(c_525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_40, c_521])).
% 5.81/2.09  tff(c_526, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_38])).
% 5.81/2.09  tff(c_653, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_526])).
% 5.81/2.09  tff(c_577, plain, (![B_204, A_205, D_206, C_207]: (k1_xboole_0=B_204 | v1_funct_1(k2_partfun1(A_205, B_204, D_206, C_207)) | ~r1_tarski(C_207, A_205) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))) | ~v1_funct_2(D_206, A_205, B_204) | ~v1_funct_1(D_206))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.09  tff(c_579, plain, (![C_207]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_207)) | ~r1_tarski(C_207, u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_577])).
% 5.81/2.09  tff(c_582, plain, (![C_207]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_207)) | ~r1_tarski(C_207, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_579])).
% 5.81/2.09  tff(c_583, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_582])).
% 5.81/2.09  tff(c_596, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_583, c_22])).
% 5.81/2.09  tff(c_602, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_596])).
% 5.81/2.09  tff(c_603, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_602])).
% 5.81/2.09  tff(c_607, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_603])).
% 5.81/2.09  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_607])).
% 5.81/2.09  tff(c_613, plain, (u1_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_582])).
% 5.81/2.09  tff(c_823, plain, (![A_263, E_262, C_264, D_266, B_265]: (k3_tmap_1(A_263, B_265, C_264, D_266, E_262)=k2_partfun1(u1_struct_0(C_264), u1_struct_0(B_265), E_262, u1_struct_0(D_266)) | ~m1_pre_topc(D_266, C_264) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_264), u1_struct_0(B_265)))) | ~v1_funct_2(E_262, u1_struct_0(C_264), u1_struct_0(B_265)) | ~v1_funct_1(E_262) | ~m1_pre_topc(D_266, A_263) | ~m1_pre_topc(C_264, A_263) | ~l1_pre_topc(B_265) | ~v2_pre_topc(B_265) | v2_struct_0(B_265) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.81/2.09  tff(c_833, plain, (![A_263, D_266]: (k3_tmap_1(A_263, '#skF_2', '#skF_3', D_266, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_266)) | ~m1_pre_topc(D_266, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_266, A_263) | ~m1_pre_topc('#skF_3', A_263) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(resolution, [status(thm)], [c_42, c_823])).
% 5.81/2.09  tff(c_842, plain, (![A_263, D_266]: (k3_tmap_1(A_263, '#skF_2', '#skF_3', D_266, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_266)) | ~m1_pre_topc(D_266, '#skF_3') | ~m1_pre_topc(D_266, A_263) | ~m1_pre_topc('#skF_3', A_263) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_833])).
% 5.81/2.09  tff(c_844, plain, (![A_267, D_268]: (k3_tmap_1(A_267, '#skF_2', '#skF_3', D_268, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_268)) | ~m1_pre_topc(D_268, '#skF_3') | ~m1_pre_topc(D_268, A_267) | ~m1_pre_topc('#skF_3', A_267) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(negUnitSimplification, [status(thm)], [c_62, c_842])).
% 5.81/2.09  tff(c_848, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_844])).
% 5.81/2.09  tff(c_856, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_40, c_848])).
% 5.81/2.09  tff(c_857, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_856])).
% 5.81/2.09  tff(c_6, plain, (![B_2, A_1, D_4, C_3]: (k1_xboole_0=B_2 | m1_subset_1(k2_partfun1(A_1, B_2, D_4, C_3), k1_zfmisc_1(k2_zfmisc_1(C_3, B_2))) | ~r1_tarski(C_3, A_1) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.09  tff(c_875, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_857, c_6])).
% 5.81/2.09  tff(c_892, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_875])).
% 5.81/2.09  tff(c_893, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_653, c_613, c_892])).
% 5.81/2.09  tff(c_900, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_893])).
% 5.81/2.09  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_40, c_900])).
% 5.81/2.09  tff(c_905, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_526])).
% 5.81/2.09  tff(c_919, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_905])).
% 5.81/2.09  tff(c_1188, plain, (![D_335, B_334, E_331, C_333, A_332]: (k3_tmap_1(A_332, B_334, C_333, D_335, E_331)=k2_partfun1(u1_struct_0(C_333), u1_struct_0(B_334), E_331, u1_struct_0(D_335)) | ~m1_pre_topc(D_335, C_333) | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_333), u1_struct_0(B_334)))) | ~v1_funct_2(E_331, u1_struct_0(C_333), u1_struct_0(B_334)) | ~v1_funct_1(E_331) | ~m1_pre_topc(D_335, A_332) | ~m1_pre_topc(C_333, A_332) | ~l1_pre_topc(B_334) | ~v2_pre_topc(B_334) | v2_struct_0(B_334) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.81/2.09  tff(c_1200, plain, (![A_332, D_335]: (k3_tmap_1(A_332, '#skF_2', '#skF_3', D_335, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_335)) | ~m1_pre_topc(D_335, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_335, A_332) | ~m1_pre_topc('#skF_3', A_332) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(resolution, [status(thm)], [c_42, c_1188])).
% 5.81/2.09  tff(c_1213, plain, (![A_332, D_335]: (k3_tmap_1(A_332, '#skF_2', '#skF_3', D_335, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_335)) | ~m1_pre_topc(D_335, '#skF_3') | ~m1_pre_topc(D_335, A_332) | ~m1_pre_topc('#skF_3', A_332) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_1200])).
% 5.81/2.09  tff(c_1215, plain, (![A_336, D_337]: (k3_tmap_1(A_336, '#skF_2', '#skF_3', D_337, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_337)) | ~m1_pre_topc(D_337, '#skF_3') | ~m1_pre_topc(D_337, A_336) | ~m1_pre_topc('#skF_3', A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(negUnitSimplification, [status(thm)], [c_62, c_1213])).
% 5.81/2.09  tff(c_1219, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1215])).
% 5.81/2.09  tff(c_1227, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_40, c_1219])).
% 5.81/2.09  tff(c_1228, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_1227])).
% 5.81/2.09  tff(c_615, plain, (![B_209, A_210, D_211, C_212]: (k1_xboole_0=B_209 | v1_funct_2(k2_partfun1(A_210, B_209, D_211, C_212), C_212, B_209) | ~r1_tarski(C_212, A_210) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))) | ~v1_funct_2(D_211, A_210, B_209) | ~v1_funct_1(D_211))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.09  tff(c_617, plain, (![C_212]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_212), C_212, u1_struct_0('#skF_2')) | ~r1_tarski(C_212, u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_615])).
% 5.81/2.09  tff(c_620, plain, (![C_212]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_212), C_212, u1_struct_0('#skF_2')) | ~r1_tarski(C_212, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_617])).
% 5.81/2.09  tff(c_621, plain, (![C_212]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', C_212), C_212, u1_struct_0('#skF_2')) | ~r1_tarski(C_212, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_613, c_620])).
% 5.81/2.09  tff(c_1254, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1228, c_621])).
% 5.81/2.09  tff(c_1275, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_919, c_1254])).
% 5.81/2.09  tff(c_1282, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1275])).
% 5.81/2.09  tff(c_1286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_40, c_1282])).
% 5.81/2.09  tff(c_1287, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_905])).
% 5.81/2.09  tff(c_1707, plain, (~v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1287])).
% 5.81/2.09  tff(c_1723, plain, (~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1420, c_1707])).
% 5.81/2.09  tff(c_1726, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1723])).
% 5.81/2.09  tff(c_1728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1726])).
% 5.81/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.09  
% 5.81/2.09  Inference rules
% 5.81/2.09  ----------------------
% 5.81/2.09  #Ref     : 0
% 5.81/2.09  #Sup     : 319
% 5.81/2.09  #Fact    : 0
% 5.81/2.09  #Define  : 0
% 5.81/2.09  #Split   : 16
% 5.81/2.09  #Chain   : 0
% 5.81/2.09  #Close   : 0
% 5.81/2.09  
% 5.81/2.09  Ordering : KBO
% 5.81/2.09  
% 5.81/2.09  Simplification rules
% 5.81/2.09  ----------------------
% 5.81/2.09  #Subsume      : 56
% 5.81/2.09  #Demod        : 455
% 5.81/2.09  #Tautology    : 46
% 5.81/2.09  #SimpNegUnit  : 120
% 5.81/2.09  #BackRed      : 15
% 5.81/2.09  
% 5.81/2.09  #Partial instantiations: 0
% 5.81/2.09  #Strategies tried      : 1
% 5.81/2.09  
% 5.81/2.09  Timing (in seconds)
% 5.81/2.09  ----------------------
% 5.81/2.09  Preprocessing        : 0.39
% 5.81/2.09  Parsing              : 0.21
% 5.81/2.09  CNF conversion       : 0.04
% 5.81/2.09  Main loop            : 0.91
% 5.81/2.09  Inferencing          : 0.30
% 5.81/2.09  Reduction            : 0.28
% 5.81/2.09  Demodulation         : 0.20
% 5.81/2.09  BG Simplification    : 0.04
% 5.81/2.09  Subsumption          : 0.23
% 5.81/2.10  Abstraction          : 0.04
% 5.81/2.10  MUC search           : 0.00
% 5.81/2.10  Cooper               : 0.00
% 5.81/2.10  Total                : 1.36
% 5.81/2.10  Index Insertion      : 0.00
% 5.81/2.10  Index Deletion       : 0.00
% 5.81/2.10  Index Matching       : 0.00
% 5.81/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
