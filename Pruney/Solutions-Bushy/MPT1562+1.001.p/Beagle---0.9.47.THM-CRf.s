%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1562+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:04 EST 2020

% Result     : Theorem 32.47s
% Output     : CNFRefutation 32.47s
% Verified   : 
% Statistics : Number of formulae       :  200 (310008 expanded)
%              Number of leaves         :   39 (111317 expanded)
%              Depth                    :   33
%              Number of atoms          :  820 (2073447 expanded)
%              Number of equality atoms :   73 (143644 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k7_domain_1 > k12_lattice3 > k2_yellow_0 > k2_tarski > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_196,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_yellow_0(A,k7_domain_1(u1_struct_0(A),B,C)) = k12_lattice3(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_yellow_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

tff(f_177,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) ) )
                    & ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) )
                     => r1_lattice3(A,k2_tarski(C,D),B) )
                    & ( r2_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) ) )
                    & ( ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) )
                     => r2_lattice3(A,k2_tarski(C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

tff(c_70,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_74,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_72,plain,(
    v2_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k12_lattice3(A_14,B_15,C_16),u1_struct_0(A_14))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_357,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_orders_2(A_200,k12_lattice3(A_200,B_201,C_202),B_201)
      | ~ m1_subset_1(k12_lattice3(A_200,B_201,C_202),u1_struct_0(A_200))
      | ~ m1_subset_1(C_202,u1_struct_0(A_200))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200)
      | ~ v2_lattice3(A_200)
      | ~ v5_orders_2(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_360,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_orders_2(A_14,k12_lattice3(A_14,B_15,C_16),B_15)
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_357])).

tff(c_343,plain,(
    ! [A_190,B_191,C_192] :
      ( r1_orders_2(A_190,k12_lattice3(A_190,B_191,C_192),C_192)
      | ~ m1_subset_1(k12_lattice3(A_190,B_191,C_192),u1_struct_0(A_190))
      | ~ m1_subset_1(C_192,u1_struct_0(A_190))
      | ~ m1_subset_1(B_191,u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | ~ v2_lattice3(A_190)
      | ~ v5_orders_2(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_346,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_orders_2(A_14,k12_lattice3(A_14,B_15,C_16),C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_343])).

tff(c_496,plain,(
    ! [A_263,E_264,B_265,C_266] :
      ( r1_orders_2(A_263,E_264,k12_lattice3(A_263,B_265,C_266))
      | ~ r1_orders_2(A_263,E_264,C_266)
      | ~ r1_orders_2(A_263,E_264,B_265)
      | ~ m1_subset_1(E_264,u1_struct_0(A_263))
      | ~ m1_subset_1(k12_lattice3(A_263,B_265,C_266),u1_struct_0(A_263))
      | ~ m1_subset_1(C_266,u1_struct_0(A_263))
      | ~ m1_subset_1(B_265,u1_struct_0(A_263))
      | ~ l1_orders_2(A_263)
      | ~ v2_lattice3(A_263)
      | ~ v5_orders_2(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_499,plain,(
    ! [A_14,E_264,B_15,C_16] :
      ( r1_orders_2(A_14,E_264,k12_lattice3(A_14,B_15,C_16))
      | ~ r1_orders_2(A_14,E_264,C_16)
      | ~ r1_orders_2(A_14,E_264,B_15)
      | ~ m1_subset_1(E_264,u1_struct_0(A_14))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_496])).

tff(c_463,plain,(
    ! [A_253,B_254,C_255,D_256] :
      ( r1_orders_2(A_253,'#skF_4'(A_253,B_254,C_255,D_256),B_254)
      | k12_lattice3(A_253,B_254,C_255) = D_256
      | ~ r1_orders_2(A_253,D_256,C_255)
      | ~ r1_orders_2(A_253,D_256,B_254)
      | ~ m1_subset_1(D_256,u1_struct_0(A_253))
      | ~ m1_subset_1(C_255,u1_struct_0(A_253))
      | ~ m1_subset_1(B_254,u1_struct_0(A_253))
      | ~ l1_orders_2(A_253)
      | ~ v2_lattice3(A_253)
      | ~ v5_orders_2(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    ! [A_47,B_71,C_83,D_89] :
      ( ~ r1_orders_2(A_47,'#skF_4'(A_47,B_71,C_83,D_89),D_89)
      | k12_lattice3(A_47,B_71,C_83) = D_89
      | ~ r1_orders_2(A_47,D_89,C_83)
      | ~ r1_orders_2(A_47,D_89,B_71)
      | ~ m1_subset_1(D_89,u1_struct_0(A_47))
      | ~ m1_subset_1(C_83,u1_struct_0(A_47))
      | ~ m1_subset_1(B_71,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | ~ v2_lattice3(A_47)
      | ~ v5_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_469,plain,(
    ! [A_257,B_258,C_259] :
      ( k12_lattice3(A_257,B_258,C_259) = B_258
      | ~ r1_orders_2(A_257,B_258,C_259)
      | ~ r1_orders_2(A_257,B_258,B_258)
      | ~ m1_subset_1(C_259,u1_struct_0(A_257))
      | ~ m1_subset_1(B_258,u1_struct_0(A_257))
      | ~ l1_orders_2(A_257)
      | ~ v2_lattice3(A_257)
      | ~ v5_orders_2(A_257) ) ),
    inference(resolution,[status(thm)],[c_463,c_34])).

tff(c_575,plain,(
    ! [A_286,B_287,C_288] :
      ( k12_lattice3(A_286,k12_lattice3(A_286,B_287,C_288),C_288) = k12_lattice3(A_286,B_287,C_288)
      | ~ r1_orders_2(A_286,k12_lattice3(A_286,B_287,C_288),k12_lattice3(A_286,B_287,C_288))
      | ~ m1_subset_1(k12_lattice3(A_286,B_287,C_288),u1_struct_0(A_286))
      | ~ m1_subset_1(C_288,u1_struct_0(A_286))
      | ~ m1_subset_1(B_287,u1_struct_0(A_286))
      | ~ l1_orders_2(A_286)
      | ~ v2_lattice3(A_286)
      | ~ v5_orders_2(A_286) ) ),
    inference(resolution,[status(thm)],[c_346,c_469])).

tff(c_4346,plain,(
    ! [A_488,B_489,C_490] :
      ( k12_lattice3(A_488,k12_lattice3(A_488,B_489,C_490),C_490) = k12_lattice3(A_488,B_489,C_490)
      | ~ r1_orders_2(A_488,k12_lattice3(A_488,B_489,C_490),C_490)
      | ~ r1_orders_2(A_488,k12_lattice3(A_488,B_489,C_490),B_489)
      | ~ m1_subset_1(k12_lattice3(A_488,B_489,C_490),u1_struct_0(A_488))
      | ~ m1_subset_1(C_490,u1_struct_0(A_488))
      | ~ m1_subset_1(B_489,u1_struct_0(A_488))
      | ~ l1_orders_2(A_488)
      | ~ v2_lattice3(A_488)
      | ~ v5_orders_2(A_488) ) ),
    inference(resolution,[status(thm)],[c_499,c_575])).

tff(c_23388,plain,(
    ! [A_862,B_863,C_864] :
      ( k12_lattice3(A_862,k12_lattice3(A_862,B_863,C_864),C_864) = k12_lattice3(A_862,B_863,C_864)
      | ~ r1_orders_2(A_862,k12_lattice3(A_862,B_863,C_864),B_863)
      | ~ m1_subset_1(k12_lattice3(A_862,B_863,C_864),u1_struct_0(A_862))
      | ~ m1_subset_1(C_864,u1_struct_0(A_862))
      | ~ m1_subset_1(B_863,u1_struct_0(A_862))
      | ~ l1_orders_2(A_862)
      | ~ v2_lattice3(A_862)
      | ~ v5_orders_2(A_862) ) ),
    inference(resolution,[status(thm)],[c_346,c_4346])).

tff(c_23494,plain,(
    ! [A_865,B_866,C_867] :
      ( k12_lattice3(A_865,k12_lattice3(A_865,B_866,C_867),C_867) = k12_lattice3(A_865,B_866,C_867)
      | ~ m1_subset_1(k12_lattice3(A_865,B_866,C_867),u1_struct_0(A_865))
      | ~ m1_subset_1(C_867,u1_struct_0(A_865))
      | ~ m1_subset_1(B_866,u1_struct_0(A_865))
      | ~ l1_orders_2(A_865)
      | ~ v2_lattice3(A_865)
      | ~ v5_orders_2(A_865) ) ),
    inference(resolution,[status(thm)],[c_360,c_23388])).

tff(c_23576,plain,(
    ! [A_868,B_869,C_870] :
      ( k12_lattice3(A_868,k12_lattice3(A_868,B_869,C_870),C_870) = k12_lattice3(A_868,B_869,C_870)
      | ~ m1_subset_1(C_870,u1_struct_0(A_868))
      | ~ m1_subset_1(B_869,u1_struct_0(A_868))
      | ~ l1_orders_2(A_868)
      | ~ v2_lattice3(A_868)
      | ~ v5_orders_2(A_868) ) ),
    inference(resolution,[status(thm)],[c_14,c_23494])).

tff(c_23594,plain,(
    ! [B_869] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_869,'#skF_7'),'#skF_7') = k12_lattice3('#skF_5',B_869,'#skF_7')
      | ~ m1_subset_1(B_869,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_23576])).

tff(c_24038,plain,(
    ! [B_875] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_875,'#skF_7'),'#skF_7') = k12_lattice3('#skF_5',B_875,'#skF_7')
      | ~ m1_subset_1(B_875,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_23594])).

tff(c_24093,plain,(
    k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7') = k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_24038])).

tff(c_24160,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24093,c_346])).

tff(c_24230,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_24160])).

tff(c_24238,plain,(
    ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_24230])).

tff(c_24241,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_24238])).

tff(c_24245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_24241])).

tff(c_24247,plain,(
    m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_24230])).

tff(c_24157,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24093,c_360])).

tff(c_24228,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_24157])).

tff(c_24472,plain,(
    r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24247,c_24228])).

tff(c_488,plain,(
    ! [A_14,B_15,C_16] :
      ( k12_lattice3(A_14,k12_lattice3(A_14,B_15,C_16),B_15) = k12_lattice3(A_14,B_15,C_16)
      | ~ r1_orders_2(A_14,k12_lattice3(A_14,B_15,C_16),k12_lattice3(A_14,B_15,C_16))
      | ~ m1_subset_1(k12_lattice3(A_14,B_15,C_16),u1_struct_0(A_14))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_360,c_469])).

tff(c_24495,plain,
    ( k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6') = k12_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_24472,c_488])).

tff(c_24534,plain,(
    k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6') = k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_24247,c_24495])).

tff(c_24608,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24534,c_346])).

tff(c_24678,plain,(
    r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_24247,c_68,c_24608])).

tff(c_24246,plain,(
    r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_24230])).

tff(c_54,plain,(
    ! [A_97,C_109,D_111,B_105] :
      ( r1_lattice3(A_97,k2_tarski(C_109,D_111),B_105)
      | ~ r1_orders_2(A_97,B_105,D_111)
      | ~ r1_orders_2(A_97,B_105,C_109)
      | ~ m1_subset_1(D_111,u1_struct_0(A_97))
      | ~ m1_subset_1(C_109,u1_struct_0(A_97))
      | ~ m1_subset_1(B_105,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_16,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_90,plain,(
    ! [A_127,B_128,C_129] :
      ( k7_domain_1(A_127,B_128,C_129) = k2_tarski(B_128,C_129)
      | ~ m1_subset_1(C_129,A_127)
      | ~ m1_subset_1(B_128,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_98,plain,(
    ! [B_128] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_128,'#skF_6') = k2_tarski(B_128,'#skF_6')
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_68,c_90])).

tff(c_100,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_18,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_104,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_18])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_109,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_109])).

tff(c_114,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,
    ( ~ v2_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_118])).

tff(c_124,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_99,plain,(
    ! [B_128] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_128,'#skF_7') = k2_tarski(B_128,'#skF_7')
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_66,c_90])).

tff(c_151,plain,(
    ! [B_133] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_133,'#skF_7') = k2_tarski(B_133,'#skF_7')
      | ~ m1_subset_1(B_133,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_99])).

tff(c_165,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_151])).

tff(c_64,plain,(
    k2_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7')) != k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_167,plain,(
    k2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) != k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_64])).

tff(c_23592,plain,(
    ! [B_869] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_869,'#skF_6'),'#skF_6') = k12_lattice3('#skF_5',B_869,'#skF_6')
      | ~ m1_subset_1(B_869,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_23576])).

tff(c_23612,plain,(
    ! [B_871] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_871,'#skF_6'),'#skF_6') = k12_lattice3('#skF_5',B_871,'#skF_6')
      | ~ m1_subset_1(B_871,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_23592])).

tff(c_23665,plain,(
    k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6') = k12_lattice3('#skF_5','#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_23612])).

tff(c_23730,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_23665,c_346])).

tff(c_23800,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_23730])).

tff(c_23808,plain,(
    ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_23800])).

tff(c_23811,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_23808])).

tff(c_23815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_68,c_23811])).

tff(c_23816,plain,(
    r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_23800])).

tff(c_23817,plain,(
    m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_23800])).

tff(c_23727,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_23665,c_360])).

tff(c_23798,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_23727])).

tff(c_25451,plain,(
    r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23817,c_23798])).

tff(c_25474,plain,
    ( k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_7') = k12_lattice3('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_25451,c_488])).

tff(c_25513,plain,(
    k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_7') = k12_lattice3('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_68,c_23817,c_25474])).

tff(c_25587,plain,
    ( r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25513,c_346])).

tff(c_25657,plain,(
    r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_23817,c_66,c_25587])).

tff(c_500,plain,(
    ! [A_267,E_268,B_269,C_270] :
      ( r1_orders_2(A_267,E_268,k12_lattice3(A_267,B_269,C_270))
      | ~ r1_orders_2(A_267,E_268,C_270)
      | ~ r1_orders_2(A_267,E_268,B_269)
      | ~ m1_subset_1(E_268,u1_struct_0(A_267))
      | ~ m1_subset_1(C_270,u1_struct_0(A_267))
      | ~ m1_subset_1(B_269,u1_struct_0(A_267))
      | ~ l1_orders_2(A_267)
      | ~ v2_lattice3(A_267)
      | ~ v5_orders_2(A_267) ) ),
    inference(resolution,[status(thm)],[c_14,c_496])).

tff(c_434,plain,(
    ! [A_242,B_243,C_244,D_245] :
      ( r1_orders_2(A_242,'#skF_4'(A_242,B_243,C_244,D_245),C_244)
      | k12_lattice3(A_242,B_243,C_244) = D_245
      | ~ r1_orders_2(A_242,D_245,C_244)
      | ~ r1_orders_2(A_242,D_245,B_243)
      | ~ m1_subset_1(D_245,u1_struct_0(A_242))
      | ~ m1_subset_1(C_244,u1_struct_0(A_242))
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ l1_orders_2(A_242)
      | ~ v2_lattice3(A_242)
      | ~ v5_orders_2(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_439,plain,(
    ! [A_242,B_243,C_244] :
      ( k12_lattice3(A_242,B_243,C_244) = C_244
      | ~ r1_orders_2(A_242,C_244,C_244)
      | ~ r1_orders_2(A_242,C_244,B_243)
      | ~ m1_subset_1(C_244,u1_struct_0(A_242))
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ l1_orders_2(A_242)
      | ~ v2_lattice3(A_242)
      | ~ v5_orders_2(A_242) ) ),
    inference(resolution,[status(thm)],[c_434,c_34])).

tff(c_1995,plain,(
    ! [A_412,B_413,B_414,C_415] :
      ( k12_lattice3(A_412,B_413,k12_lattice3(A_412,B_414,C_415)) = k12_lattice3(A_412,B_414,C_415)
      | ~ r1_orders_2(A_412,k12_lattice3(A_412,B_414,C_415),B_413)
      | ~ m1_subset_1(B_413,u1_struct_0(A_412))
      | ~ r1_orders_2(A_412,k12_lattice3(A_412,B_414,C_415),C_415)
      | ~ r1_orders_2(A_412,k12_lattice3(A_412,B_414,C_415),B_414)
      | ~ m1_subset_1(k12_lattice3(A_412,B_414,C_415),u1_struct_0(A_412))
      | ~ m1_subset_1(C_415,u1_struct_0(A_412))
      | ~ m1_subset_1(B_414,u1_struct_0(A_412))
      | ~ l1_orders_2(A_412)
      | ~ v2_lattice3(A_412)
      | ~ v5_orders_2(A_412) ) ),
    inference(resolution,[status(thm)],[c_500,c_439])).

tff(c_12003,plain,(
    ! [B_661,C_662,A_664,B_663,C_660] :
      ( k12_lattice3(A_664,k12_lattice3(A_664,B_663,C_662),k12_lattice3(A_664,B_661,C_660)) = k12_lattice3(A_664,B_661,C_660)
      | ~ m1_subset_1(k12_lattice3(A_664,B_663,C_662),u1_struct_0(A_664))
      | ~ r1_orders_2(A_664,k12_lattice3(A_664,B_661,C_660),C_660)
      | ~ r1_orders_2(A_664,k12_lattice3(A_664,B_661,C_660),B_661)
      | ~ m1_subset_1(C_660,u1_struct_0(A_664))
      | ~ m1_subset_1(B_661,u1_struct_0(A_664))
      | ~ r1_orders_2(A_664,k12_lattice3(A_664,B_661,C_660),C_662)
      | ~ r1_orders_2(A_664,k12_lattice3(A_664,B_661,C_660),B_663)
      | ~ m1_subset_1(k12_lattice3(A_664,B_661,C_660),u1_struct_0(A_664))
      | ~ m1_subset_1(C_662,u1_struct_0(A_664))
      | ~ m1_subset_1(B_663,u1_struct_0(A_664))
      | ~ l1_orders_2(A_664)
      | ~ v2_lattice3(A_664)
      | ~ v5_orders_2(A_664) ) ),
    inference(resolution,[status(thm)],[c_499,c_1995])).

tff(c_44051,plain,(
    ! [A_1039,B_1038,C_1040,C_1037,B_1036] :
      ( k12_lattice3(A_1039,k12_lattice3(A_1039,B_1038,C_1037),k12_lattice3(A_1039,B_1036,C_1040)) = k12_lattice3(A_1039,B_1036,C_1040)
      | ~ r1_orders_2(A_1039,k12_lattice3(A_1039,B_1036,C_1040),C_1040)
      | ~ r1_orders_2(A_1039,k12_lattice3(A_1039,B_1036,C_1040),B_1036)
      | ~ m1_subset_1(C_1040,u1_struct_0(A_1039))
      | ~ m1_subset_1(B_1036,u1_struct_0(A_1039))
      | ~ r1_orders_2(A_1039,k12_lattice3(A_1039,B_1036,C_1040),C_1037)
      | ~ r1_orders_2(A_1039,k12_lattice3(A_1039,B_1036,C_1040),B_1038)
      | ~ m1_subset_1(k12_lattice3(A_1039,B_1036,C_1040),u1_struct_0(A_1039))
      | ~ m1_subset_1(C_1037,u1_struct_0(A_1039))
      | ~ m1_subset_1(B_1038,u1_struct_0(A_1039))
      | ~ l1_orders_2(A_1039)
      | ~ v2_lattice3(A_1039)
      | ~ v5_orders_2(A_1039) ) ),
    inference(resolution,[status(thm)],[c_14,c_12003])).

tff(c_44147,plain,(
    ! [B_1038,C_1037] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_1038,C_1037),k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6')) = k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6')
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6')
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6'),C_1037)
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6'),B_1038)
      | ~ m1_subset_1(k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1037,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1038,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23665,c_44051])).

tff(c_45852,plain,(
    ! [B_1052,C_1053] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_1052,C_1053),k12_lattice3('#skF_5','#skF_7','#skF_6')) = k12_lattice3('#skF_5','#skF_7','#skF_6')
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),C_1053)
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),B_1052)
      | ~ m1_subset_1(C_1053,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1052,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_23817,c_23665,c_23665,c_23665,c_23817,c_68,c_25451,c_23665,c_23816,c_23665,c_23665,c_44147])).

tff(c_468,plain,(
    ! [A_253,B_254,C_255] :
      ( k12_lattice3(A_253,B_254,C_255) = B_254
      | ~ r1_orders_2(A_253,B_254,C_255)
      | ~ r1_orders_2(A_253,B_254,B_254)
      | ~ m1_subset_1(C_255,u1_struct_0(A_253))
      | ~ m1_subset_1(B_254,u1_struct_0(A_253))
      | ~ l1_orders_2(A_253)
      | ~ v2_lattice3(A_253)
      | ~ v5_orders_2(A_253) ) ),
    inference(resolution,[status(thm)],[c_463,c_34])).

tff(c_25478,plain,
    ( k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_7','#skF_6')) = k12_lattice3('#skF_5','#skF_7','#skF_6')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_25451,c_468])).

tff(c_25519,plain,(
    k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_7','#skF_6')) = k12_lattice3('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_23817,c_25451,c_25478])).

tff(c_44143,plain,(
    ! [B_1038,C_1037] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_1038,C_1037),k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')) = k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7'),C_1037)
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7'),B_1038)
      | ~ m1_subset_1(k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1037,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1038,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24093,c_44051])).

tff(c_44355,plain,(
    ! [B_1041,C_1042] :
      ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',B_1041,C_1042),k12_lattice3('#skF_5','#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),C_1042)
      | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),B_1041)
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1041,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_24247,c_24093,c_24093,c_24093,c_24247,c_66,c_24472,c_24093,c_24246,c_24093,c_24093,c_44143])).

tff(c_44612,plain,
    ( k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25519,c_44355])).

tff(c_44888,plain,
    ( k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23817,c_23817,c_44612])).

tff(c_44944,plain,(
    ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_44888])).

tff(c_44947,plain,
    ( ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_499,c_44944])).

tff(c_44951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_68,c_24247,c_24246,c_24678,c_44947])).

tff(c_44952,plain,(
    k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44888])).

tff(c_45058,plain,
    ( k12_lattice3('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_6','#skF_7')),k12_lattice3('#skF_5','#skF_7','#skF_6')) = k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_6','#skF_7')),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44952,c_488])).

tff(c_45161,plain,(
    k12_lattice3('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_7','#skF_6')) = k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_23817,c_24247,c_24247,c_44952,c_24472,c_44952,c_44952,c_44952,c_45058])).

tff(c_45861,plain,
    ( k12_lattice3('#skF_5','#skF_7','#skF_6') = k12_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_7')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45852,c_45161])).

tff(c_46221,plain,(
    k12_lattice3('#skF_5','#skF_7','#skF_6') = k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_23816,c_25657,c_45861])).

tff(c_8,plain,(
    ! [A_2,B_9,C_10] :
      ( m1_subset_1('#skF_1'(A_2,B_9,C_10),u1_struct_0(A_2))
      | k2_yellow_0(A_2,B_9) = C_10
      | ~ r1_lattice3(A_2,B_9,C_10)
      | ~ r2_yellow_0(A_2,B_9)
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_304,plain,(
    ! [A_177,B_178,C_179] :
      ( r1_lattice3(A_177,B_178,'#skF_1'(A_177,B_178,C_179))
      | k2_yellow_0(A_177,B_178) = C_179
      | ~ r1_lattice3(A_177,B_178,C_179)
      | ~ r2_yellow_0(A_177,B_178)
      | ~ m1_subset_1(C_179,u1_struct_0(A_177))
      | ~ l1_orders_2(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_97,B_105,D_111,C_109] :
      ( r1_orders_2(A_97,B_105,D_111)
      | ~ r1_lattice3(A_97,k2_tarski(C_109,D_111),B_105)
      | ~ m1_subset_1(D_111,u1_struct_0(A_97))
      | ~ m1_subset_1(C_109,u1_struct_0(A_97))
      | ~ m1_subset_1(B_105,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_763,plain,(
    ! [A_359,C_360,D_361,C_362] :
      ( r1_orders_2(A_359,'#skF_1'(A_359,k2_tarski(C_360,D_361),C_362),D_361)
      | ~ m1_subset_1(D_361,u1_struct_0(A_359))
      | ~ m1_subset_1(C_360,u1_struct_0(A_359))
      | ~ m1_subset_1('#skF_1'(A_359,k2_tarski(C_360,D_361),C_362),u1_struct_0(A_359))
      | k2_yellow_0(A_359,k2_tarski(C_360,D_361)) = C_362
      | ~ r1_lattice3(A_359,k2_tarski(C_360,D_361),C_362)
      | ~ r2_yellow_0(A_359,k2_tarski(C_360,D_361))
      | ~ m1_subset_1(C_362,u1_struct_0(A_359))
      | ~ l1_orders_2(A_359) ) ),
    inference(resolution,[status(thm)],[c_304,c_60])).

tff(c_767,plain,(
    ! [A_2,C_360,D_361,C_10] :
      ( r1_orders_2(A_2,'#skF_1'(A_2,k2_tarski(C_360,D_361),C_10),D_361)
      | ~ m1_subset_1(D_361,u1_struct_0(A_2))
      | ~ m1_subset_1(C_360,u1_struct_0(A_2))
      | k2_yellow_0(A_2,k2_tarski(C_360,D_361)) = C_10
      | ~ r1_lattice3(A_2,k2_tarski(C_360,D_361),C_10)
      | ~ r2_yellow_0(A_2,k2_tarski(C_360,D_361))
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_8,c_763])).

tff(c_62,plain,(
    ! [A_97,B_105,C_109,D_111] :
      ( r1_orders_2(A_97,B_105,C_109)
      | ~ r1_lattice3(A_97,k2_tarski(C_109,D_111),B_105)
      | ~ m1_subset_1(D_111,u1_struct_0(A_97))
      | ~ m1_subset_1(C_109,u1_struct_0(A_97))
      | ~ m1_subset_1(B_105,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_982,plain,(
    ! [A_369,C_370,D_371,C_372] :
      ( r1_orders_2(A_369,'#skF_1'(A_369,k2_tarski(C_370,D_371),C_372),C_370)
      | ~ m1_subset_1(D_371,u1_struct_0(A_369))
      | ~ m1_subset_1(C_370,u1_struct_0(A_369))
      | ~ m1_subset_1('#skF_1'(A_369,k2_tarski(C_370,D_371),C_372),u1_struct_0(A_369))
      | k2_yellow_0(A_369,k2_tarski(C_370,D_371)) = C_372
      | ~ r1_lattice3(A_369,k2_tarski(C_370,D_371),C_372)
      | ~ r2_yellow_0(A_369,k2_tarski(C_370,D_371))
      | ~ m1_subset_1(C_372,u1_struct_0(A_369))
      | ~ l1_orders_2(A_369) ) ),
    inference(resolution,[status(thm)],[c_304,c_62])).

tff(c_986,plain,(
    ! [A_2,C_370,D_371,C_10] :
      ( r1_orders_2(A_2,'#skF_1'(A_2,k2_tarski(C_370,D_371),C_10),C_370)
      | ~ m1_subset_1(D_371,u1_struct_0(A_2))
      | ~ m1_subset_1(C_370,u1_struct_0(A_2))
      | k2_yellow_0(A_2,k2_tarski(C_370,D_371)) = C_10
      | ~ r1_lattice3(A_2,k2_tarski(C_370,D_371),C_10)
      | ~ r2_yellow_0(A_2,k2_tarski(C_370,D_371))
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_8,c_982])).

tff(c_4,plain,(
    ! [A_2,B_9,C_10] :
      ( ~ r1_orders_2(A_2,'#skF_1'(A_2,B_9,C_10),C_10)
      | k2_yellow_0(A_2,B_9) = C_10
      | ~ r1_lattice3(A_2,B_9,C_10)
      | ~ r2_yellow_0(A_2,B_9)
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2871,plain,(
    ! [A_438,B_439,B_440,C_441] :
      ( k2_yellow_0(A_438,B_439) = k12_lattice3(A_438,B_440,C_441)
      | ~ r1_lattice3(A_438,B_439,k12_lattice3(A_438,B_440,C_441))
      | ~ r2_yellow_0(A_438,B_439)
      | ~ m1_subset_1(k12_lattice3(A_438,B_440,C_441),u1_struct_0(A_438))
      | ~ r1_orders_2(A_438,'#skF_1'(A_438,B_439,k12_lattice3(A_438,B_440,C_441)),C_441)
      | ~ r1_orders_2(A_438,'#skF_1'(A_438,B_439,k12_lattice3(A_438,B_440,C_441)),B_440)
      | ~ m1_subset_1('#skF_1'(A_438,B_439,k12_lattice3(A_438,B_440,C_441)),u1_struct_0(A_438))
      | ~ m1_subset_1(C_441,u1_struct_0(A_438))
      | ~ m1_subset_1(B_440,u1_struct_0(A_438))
      | ~ l1_orders_2(A_438)
      | ~ v2_lattice3(A_438)
      | ~ v5_orders_2(A_438) ) ),
    inference(resolution,[status(thm)],[c_500,c_4])).

tff(c_10228,plain,(
    ! [A_620,C_621,D_622,B_623] :
      ( ~ r1_orders_2(A_620,'#skF_1'(A_620,k2_tarski(C_621,D_622),k12_lattice3(A_620,B_623,C_621)),B_623)
      | ~ m1_subset_1('#skF_1'(A_620,k2_tarski(C_621,D_622),k12_lattice3(A_620,B_623,C_621)),u1_struct_0(A_620))
      | ~ m1_subset_1(B_623,u1_struct_0(A_620))
      | ~ v2_lattice3(A_620)
      | ~ v5_orders_2(A_620)
      | ~ m1_subset_1(D_622,u1_struct_0(A_620))
      | ~ m1_subset_1(C_621,u1_struct_0(A_620))
      | k2_yellow_0(A_620,k2_tarski(C_621,D_622)) = k12_lattice3(A_620,B_623,C_621)
      | ~ r1_lattice3(A_620,k2_tarski(C_621,D_622),k12_lattice3(A_620,B_623,C_621))
      | ~ r2_yellow_0(A_620,k2_tarski(C_621,D_622))
      | ~ m1_subset_1(k12_lattice3(A_620,B_623,C_621),u1_struct_0(A_620))
      | ~ l1_orders_2(A_620) ) ),
    inference(resolution,[status(thm)],[c_986,c_2871])).

tff(c_10297,plain,(
    ! [A_2,C_360,D_361] :
      ( ~ m1_subset_1('#skF_1'(A_2,k2_tarski(C_360,D_361),k12_lattice3(A_2,D_361,C_360)),u1_struct_0(A_2))
      | ~ v2_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ m1_subset_1(D_361,u1_struct_0(A_2))
      | ~ m1_subset_1(C_360,u1_struct_0(A_2))
      | k2_yellow_0(A_2,k2_tarski(C_360,D_361)) = k12_lattice3(A_2,D_361,C_360)
      | ~ r1_lattice3(A_2,k2_tarski(C_360,D_361),k12_lattice3(A_2,D_361,C_360))
      | ~ r2_yellow_0(A_2,k2_tarski(C_360,D_361))
      | ~ m1_subset_1(k12_lattice3(A_2,D_361,C_360),u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_767,c_10228])).

tff(c_46559,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | k2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_7','#skF_6')
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_46221,c_10297])).

tff(c_46655,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | k2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24247,c_46221,c_46221,c_46221,c_68,c_66,c_74,c_72,c_46559])).

tff(c_46656,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_46655])).

tff(c_47559,plain,(
    ~ r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46656])).

tff(c_32,plain,(
    ! [A_22,B_36,C_43] :
      ( m1_subset_1('#skF_2'(A_22,B_36,C_43),u1_struct_0(A_22))
      | r2_yellow_0(A_22,B_36)
      | ~ r1_lattice3(A_22,B_36,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_22,B_36,C_43] :
      ( r1_lattice3(A_22,B_36,'#skF_2'(A_22,B_36,C_43))
      | r2_yellow_0(A_22,B_36)
      | ~ r1_lattice3(A_22,B_36,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_276,plain,(
    ! [A_166,B_167,D_168,C_169] :
      ( r1_orders_2(A_166,B_167,D_168)
      | ~ r1_lattice3(A_166,k2_tarski(C_169,D_168),B_167)
      | ~ m1_subset_1(D_168,u1_struct_0(A_166))
      | ~ m1_subset_1(C_169,u1_struct_0(A_166))
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_orders_2(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_581,plain,(
    ! [A_289,C_290,D_291,C_292] :
      ( r1_orders_2(A_289,'#skF_2'(A_289,k2_tarski(C_290,D_291),C_292),D_291)
      | ~ m1_subset_1(D_291,u1_struct_0(A_289))
      | ~ m1_subset_1(C_290,u1_struct_0(A_289))
      | ~ m1_subset_1('#skF_2'(A_289,k2_tarski(C_290,D_291),C_292),u1_struct_0(A_289))
      | r2_yellow_0(A_289,k2_tarski(C_290,D_291))
      | ~ r1_lattice3(A_289,k2_tarski(C_290,D_291),C_292)
      | ~ m1_subset_1(C_292,u1_struct_0(A_289))
      | ~ l1_orders_2(A_289)
      | ~ v5_orders_2(A_289) ) ),
    inference(resolution,[status(thm)],[c_30,c_276])).

tff(c_585,plain,(
    ! [A_22,C_290,D_291,C_43] :
      ( r1_orders_2(A_22,'#skF_2'(A_22,k2_tarski(C_290,D_291),C_43),D_291)
      | ~ m1_subset_1(D_291,u1_struct_0(A_22))
      | ~ m1_subset_1(C_290,u1_struct_0(A_22))
      | r2_yellow_0(A_22,k2_tarski(C_290,D_291))
      | ~ r1_lattice3(A_22,k2_tarski(C_290,D_291),C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_581])).

tff(c_293,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( r1_orders_2(A_173,B_174,C_175)
      | ~ r1_lattice3(A_173,k2_tarski(C_175,D_176),B_174)
      | ~ m1_subset_1(D_176,u1_struct_0(A_173))
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_601,plain,(
    ! [A_300,C_301,D_302,C_303] :
      ( r1_orders_2(A_300,'#skF_2'(A_300,k2_tarski(C_301,D_302),C_303),C_301)
      | ~ m1_subset_1(D_302,u1_struct_0(A_300))
      | ~ m1_subset_1(C_301,u1_struct_0(A_300))
      | ~ m1_subset_1('#skF_2'(A_300,k2_tarski(C_301,D_302),C_303),u1_struct_0(A_300))
      | r2_yellow_0(A_300,k2_tarski(C_301,D_302))
      | ~ r1_lattice3(A_300,k2_tarski(C_301,D_302),C_303)
      | ~ m1_subset_1(C_303,u1_struct_0(A_300))
      | ~ l1_orders_2(A_300)
      | ~ v5_orders_2(A_300) ) ),
    inference(resolution,[status(thm)],[c_30,c_293])).

tff(c_605,plain,(
    ! [A_22,C_301,D_302,C_43] :
      ( r1_orders_2(A_22,'#skF_2'(A_22,k2_tarski(C_301,D_302),C_43),C_301)
      | ~ m1_subset_1(D_302,u1_struct_0(A_22))
      | ~ m1_subset_1(C_301,u1_struct_0(A_22))
      | r2_yellow_0(A_22,k2_tarski(C_301,D_302))
      | ~ r1_lattice3(A_22,k2_tarski(C_301,D_302),C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_601])).

tff(c_28,plain,(
    ! [A_22,B_36,C_43] :
      ( ~ r1_orders_2(A_22,'#skF_2'(A_22,B_36,C_43),C_43)
      | r2_yellow_0(A_22,B_36)
      | ~ r1_lattice3(A_22,B_36,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2299,plain,(
    ! [A_417,B_418,B_419,C_420] :
      ( r2_yellow_0(A_417,B_418)
      | ~ r1_lattice3(A_417,B_418,k12_lattice3(A_417,B_419,C_420))
      | ~ m1_subset_1(k12_lattice3(A_417,B_419,C_420),u1_struct_0(A_417))
      | ~ r1_orders_2(A_417,'#skF_2'(A_417,B_418,k12_lattice3(A_417,B_419,C_420)),C_420)
      | ~ r1_orders_2(A_417,'#skF_2'(A_417,B_418,k12_lattice3(A_417,B_419,C_420)),B_419)
      | ~ m1_subset_1('#skF_2'(A_417,B_418,k12_lattice3(A_417,B_419,C_420)),u1_struct_0(A_417))
      | ~ m1_subset_1(C_420,u1_struct_0(A_417))
      | ~ m1_subset_1(B_419,u1_struct_0(A_417))
      | ~ l1_orders_2(A_417)
      | ~ v2_lattice3(A_417)
      | ~ v5_orders_2(A_417) ) ),
    inference(resolution,[status(thm)],[c_500,c_28])).

tff(c_8044,plain,(
    ! [A_559,C_560,D_561,B_562] :
      ( ~ r1_orders_2(A_559,'#skF_2'(A_559,k2_tarski(C_560,D_561),k12_lattice3(A_559,B_562,C_560)),B_562)
      | ~ m1_subset_1('#skF_2'(A_559,k2_tarski(C_560,D_561),k12_lattice3(A_559,B_562,C_560)),u1_struct_0(A_559))
      | ~ m1_subset_1(B_562,u1_struct_0(A_559))
      | ~ v2_lattice3(A_559)
      | ~ m1_subset_1(D_561,u1_struct_0(A_559))
      | ~ m1_subset_1(C_560,u1_struct_0(A_559))
      | r2_yellow_0(A_559,k2_tarski(C_560,D_561))
      | ~ r1_lattice3(A_559,k2_tarski(C_560,D_561),k12_lattice3(A_559,B_562,C_560))
      | ~ m1_subset_1(k12_lattice3(A_559,B_562,C_560),u1_struct_0(A_559))
      | ~ l1_orders_2(A_559)
      | ~ v5_orders_2(A_559) ) ),
    inference(resolution,[status(thm)],[c_605,c_2299])).

tff(c_8114,plain,(
    ! [A_22,C_290,D_291] :
      ( ~ m1_subset_1('#skF_2'(A_22,k2_tarski(C_290,D_291),k12_lattice3(A_22,D_291,C_290)),u1_struct_0(A_22))
      | ~ v2_lattice3(A_22)
      | ~ m1_subset_1(D_291,u1_struct_0(A_22))
      | ~ m1_subset_1(C_290,u1_struct_0(A_22))
      | r2_yellow_0(A_22,k2_tarski(C_290,D_291))
      | ~ r1_lattice3(A_22,k2_tarski(C_290,D_291),k12_lattice3(A_22,D_291,C_290))
      | ~ m1_subset_1(k12_lattice3(A_22,D_291,C_290),u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_585,c_8044])).

tff(c_46574,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v2_lattice3('#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_46221,c_8114])).

tff(c_46666,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_24247,c_46221,c_46221,c_68,c_66,c_72,c_46574])).

tff(c_50821,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_47559,c_46666])).

tff(c_50822,plain,(
    ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_50821])).

tff(c_50912,plain,
    ( ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_50822])).

tff(c_50916,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24247,c_68,c_66,c_24678,c_24246,c_50912])).

tff(c_50918,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50821])).

tff(c_50917,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50821])).

tff(c_50933,plain,
    ( r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_50917])).

tff(c_50936,plain,(
    r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_24247,c_50918,c_50933])).

tff(c_50938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47559,c_50936])).

tff(c_50940,plain,(
    r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46656])).

tff(c_26,plain,(
    ! [A_22,B_36] :
      ( m1_subset_1('#skF_3'(A_22,B_36),u1_struct_0(A_22))
      | ~ r2_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [A_22,B_36] :
      ( r1_lattice3(A_22,B_36,'#skF_3'(A_22,B_36))
      | ~ r2_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_2,B_9,C_10] :
      ( r1_lattice3(A_2,B_9,'#skF_1'(A_2,B_9,C_10))
      | k2_yellow_0(A_2,B_9) = C_10
      | ~ r1_lattice3(A_2,B_9,C_10)
      | ~ r2_yellow_0(A_2,B_9)
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_22,D_46,B_36] :
      ( r1_orders_2(A_22,D_46,'#skF_3'(A_22,B_36))
      | ~ r1_lattice3(A_22,B_36,D_46)
      | ~ m1_subset_1(D_46,u1_struct_0(A_22))
      | ~ r2_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_287,plain,(
    ! [A_170,B_171,C_172] :
      ( ~ r1_orders_2(A_170,'#skF_1'(A_170,B_171,C_172),C_172)
      | k2_yellow_0(A_170,B_171) = C_172
      | ~ r1_lattice3(A_170,B_171,C_172)
      | ~ r2_yellow_0(A_170,B_171)
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ l1_orders_2(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_666,plain,(
    ! [A_333,B_334,B_335] :
      ( k2_yellow_0(A_333,B_334) = '#skF_3'(A_333,B_335)
      | ~ r1_lattice3(A_333,B_334,'#skF_3'(A_333,B_335))
      | ~ r2_yellow_0(A_333,B_334)
      | ~ m1_subset_1('#skF_3'(A_333,B_335),u1_struct_0(A_333))
      | ~ r1_lattice3(A_333,B_335,'#skF_1'(A_333,B_334,'#skF_3'(A_333,B_335)))
      | ~ m1_subset_1('#skF_1'(A_333,B_334,'#skF_3'(A_333,B_335)),u1_struct_0(A_333))
      | ~ r2_yellow_0(A_333,B_335)
      | ~ l1_orders_2(A_333)
      | ~ v5_orders_2(A_333) ) ),
    inference(resolution,[status(thm)],[c_22,c_287])).

tff(c_675,plain,(
    ! [A_336,B_337] :
      ( ~ m1_subset_1('#skF_1'(A_336,B_337,'#skF_3'(A_336,B_337)),u1_struct_0(A_336))
      | ~ v5_orders_2(A_336)
      | k2_yellow_0(A_336,B_337) = '#skF_3'(A_336,B_337)
      | ~ r1_lattice3(A_336,B_337,'#skF_3'(A_336,B_337))
      | ~ r2_yellow_0(A_336,B_337)
      | ~ m1_subset_1('#skF_3'(A_336,B_337),u1_struct_0(A_336))
      | ~ l1_orders_2(A_336) ) ),
    inference(resolution,[status(thm)],[c_6,c_666])).

tff(c_681,plain,(
    ! [A_338,B_339] :
      ( ~ v5_orders_2(A_338)
      | k2_yellow_0(A_338,B_339) = '#skF_3'(A_338,B_339)
      | ~ r1_lattice3(A_338,B_339,'#skF_3'(A_338,B_339))
      | ~ r2_yellow_0(A_338,B_339)
      | ~ m1_subset_1('#skF_3'(A_338,B_339),u1_struct_0(A_338))
      | ~ l1_orders_2(A_338) ) ),
    inference(resolution,[status(thm)],[c_8,c_675])).

tff(c_689,plain,(
    ! [A_340,B_341] :
      ( k2_yellow_0(A_340,B_341) = '#skF_3'(A_340,B_341)
      | ~ m1_subset_1('#skF_3'(A_340,B_341),u1_struct_0(A_340))
      | ~ r2_yellow_0(A_340,B_341)
      | ~ l1_orders_2(A_340)
      | ~ v5_orders_2(A_340) ) ),
    inference(resolution,[status(thm)],[c_24,c_681])).

tff(c_693,plain,(
    ! [A_22,B_36] :
      ( k2_yellow_0(A_22,B_36) = '#skF_3'(A_22,B_36)
      | ~ r2_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_689])).

tff(c_50947,plain,
    ( k2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_50940,c_693])).

tff(c_50956,plain,(
    k2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_50947])).

tff(c_50957,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) != k12_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50956,c_167])).

tff(c_50939,plain,
    ( ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_46656])).

tff(c_51927,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_50939])).

tff(c_51930,plain,
    ( k2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r2_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_51927])).

tff(c_51933,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) = k12_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24247,c_50940,c_50956,c_51930])).

tff(c_51934,plain,(
    ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_50957,c_51933])).

tff(c_51937,plain,
    ( ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_51934])).

tff(c_51941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24247,c_68,c_66,c_24678,c_24246,c_51937])).

tff(c_51942,plain,(
    ~ r1_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k12_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50939])).

tff(c_51946,plain,
    ( ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ r1_orders_2('#skF_5',k12_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k12_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_51942])).

tff(c_51950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24247,c_68,c_66,c_24678,c_24246,c_51946])).

%------------------------------------------------------------------------------
