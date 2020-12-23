%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:07 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 287 expanded)
%              Number of leaves         :   49 ( 121 expanded)
%              Depth                    :   18
%              Number of atoms          :  353 (1330 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_waybel_0 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > o_2_4_waybel_9 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(o_2_4_waybel_9,type,(
    o_2_4_waybel_9: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_202,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_4_waybel_9(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_4_waybel_9)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k2_waybel_0(A,B,C) = k3_funct_2(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,B)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ? [B] :
          ( l1_waybel_0(B,A)
          & ~ v2_struct_0(B)
          & v3_orders_2(B)
          & v4_orders_2(B)
          & v5_orders_2(B)
          & v6_waybel_0(B,A)
          & v7_waybel_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_waybel_0)).

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
             => r2_waybel_0(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_66,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_62,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_36,plain,(
    ! [A_137,B_138] :
      ( v1_funct_2(u1_waybel_0(A_137,B_138),u1_struct_0(B_138),u1_struct_0(A_137))
      | ~ l1_waybel_0(B_138,A_137)
      | ~ l1_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    ! [A_137,B_138] :
      ( v1_funct_1(u1_waybel_0(A_137,B_138))
      | ~ l1_waybel_0(B_138,A_137)
      | ~ l1_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_83,plain,(
    ! [B_165,A_166] :
      ( l1_orders_2(B_165)
      | ~ l1_waybel_0(B_165,A_166)
      | ~ l1_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_89,plain,
    ( l1_orders_2('#skF_8')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_83])).

tff(c_93,plain,(
    l1_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_89])).

tff(c_8,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    ! [A_151,B_152] :
      ( m1_subset_1(o_2_4_waybel_9(A_151,B_152),u1_struct_0(B_152))
      | ~ l1_waybel_0(B_152,A_151)
      | v2_struct_0(B_152)
      | ~ l1_struct_0(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_34,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1(u1_waybel_0(A_137,B_138),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_138),u1_struct_0(A_137))))
      | ~ l1_waybel_0(B_138,A_137)
      | ~ l1_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_18,plain,(
    ! [A_21,B_49,C_63,D_70] :
      ( m1_subset_1('#skF_2'(A_21,B_49,C_63,D_70),u1_struct_0(B_49))
      | r1_waybel_0(A_21,B_49,C_63)
      | ~ m1_subset_1(D_70,u1_struct_0(B_49))
      | ~ l1_waybel_0(B_49,A_21)
      | v2_struct_0(B_49)
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [B_131,A_127,C_133] :
      ( k3_funct_2(u1_struct_0(B_131),u1_struct_0(A_127),u1_waybel_0(A_127,B_131),C_133) = k2_waybel_0(A_127,B_131,C_133)
      | ~ m1_subset_1(C_133,u1_struct_0(B_131))
      | ~ l1_waybel_0(B_131,A_127)
      | v2_struct_0(B_131)
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_142,plain,(
    ! [A_222,B_223,D_224,C_225] :
      ( r2_hidden(k3_funct_2(A_222,B_223,D_224,C_225),k2_relset_1(A_222,B_223,D_224))
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_2(D_224,A_222,B_223)
      | ~ v1_funct_1(D_224)
      | ~ m1_subset_1(C_225,A_222)
      | v1_xboole_0(B_223)
      | v1_xboole_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_265,plain,(
    ! [A_304,B_305,C_306] :
      ( r2_hidden(k2_waybel_0(A_304,B_305,C_306),k2_relset_1(u1_struct_0(B_305),u1_struct_0(A_304),u1_waybel_0(A_304,B_305)))
      | ~ m1_subset_1(u1_waybel_0(A_304,B_305),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_305),u1_struct_0(A_304))))
      | ~ v1_funct_2(u1_waybel_0(A_304,B_305),u1_struct_0(B_305),u1_struct_0(A_304))
      | ~ v1_funct_1(u1_waybel_0(A_304,B_305))
      | ~ m1_subset_1(C_306,u1_struct_0(B_305))
      | v1_xboole_0(u1_struct_0(A_304))
      | v1_xboole_0(u1_struct_0(B_305))
      | ~ m1_subset_1(C_306,u1_struct_0(B_305))
      | ~ l1_waybel_0(B_305,A_304)
      | v2_struct_0(B_305)
      | ~ l1_struct_0(A_304)
      | v2_struct_0(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_142])).

tff(c_14,plain,(
    ! [A_21,B_49,C_63,D_70] :
      ( ~ r2_hidden(k2_waybel_0(A_21,B_49,'#skF_2'(A_21,B_49,C_63,D_70)),C_63)
      | r1_waybel_0(A_21,B_49,C_63)
      | ~ m1_subset_1(D_70,u1_struct_0(B_49))
      | ~ l1_waybel_0(B_49,A_21)
      | v2_struct_0(B_49)
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_285,plain,(
    ! [A_307,B_308,D_309] :
      ( r1_waybel_0(A_307,B_308,k2_relset_1(u1_struct_0(B_308),u1_struct_0(A_307),u1_waybel_0(A_307,B_308)))
      | ~ m1_subset_1(D_309,u1_struct_0(B_308))
      | ~ m1_subset_1(u1_waybel_0(A_307,B_308),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_308),u1_struct_0(A_307))))
      | ~ v1_funct_2(u1_waybel_0(A_307,B_308),u1_struct_0(B_308),u1_struct_0(A_307))
      | ~ v1_funct_1(u1_waybel_0(A_307,B_308))
      | v1_xboole_0(u1_struct_0(A_307))
      | v1_xboole_0(u1_struct_0(B_308))
      | ~ m1_subset_1('#skF_2'(A_307,B_308,k2_relset_1(u1_struct_0(B_308),u1_struct_0(A_307),u1_waybel_0(A_307,B_308)),D_309),u1_struct_0(B_308))
      | ~ l1_waybel_0(B_308,A_307)
      | v2_struct_0(B_308)
      | ~ l1_struct_0(A_307)
      | v2_struct_0(A_307) ) ),
    inference(resolution,[status(thm)],[c_265,c_14])).

tff(c_291,plain,(
    ! [A_310,B_311,D_312] :
      ( ~ m1_subset_1(u1_waybel_0(A_310,B_311),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_311),u1_struct_0(A_310))))
      | ~ v1_funct_2(u1_waybel_0(A_310,B_311),u1_struct_0(B_311),u1_struct_0(A_310))
      | ~ v1_funct_1(u1_waybel_0(A_310,B_311))
      | v1_xboole_0(u1_struct_0(A_310))
      | v1_xboole_0(u1_struct_0(B_311))
      | r1_waybel_0(A_310,B_311,k2_relset_1(u1_struct_0(B_311),u1_struct_0(A_310),u1_waybel_0(A_310,B_311)))
      | ~ m1_subset_1(D_312,u1_struct_0(B_311))
      | ~ l1_waybel_0(B_311,A_310)
      | v2_struct_0(B_311)
      | ~ l1_struct_0(A_310)
      | v2_struct_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_18,c_285])).

tff(c_295,plain,(
    ! [A_313,B_314,D_315] :
      ( ~ v1_funct_2(u1_waybel_0(A_313,B_314),u1_struct_0(B_314),u1_struct_0(A_313))
      | ~ v1_funct_1(u1_waybel_0(A_313,B_314))
      | v1_xboole_0(u1_struct_0(A_313))
      | v1_xboole_0(u1_struct_0(B_314))
      | r1_waybel_0(A_313,B_314,k2_relset_1(u1_struct_0(B_314),u1_struct_0(A_313),u1_waybel_0(A_313,B_314)))
      | ~ m1_subset_1(D_315,u1_struct_0(B_314))
      | v2_struct_0(B_314)
      | v2_struct_0(A_313)
      | ~ l1_waybel_0(B_314,A_313)
      | ~ l1_struct_0(A_313) ) ),
    inference(resolution,[status(thm)],[c_34,c_291])).

tff(c_317,plain,(
    ! [A_320,B_321,A_322] :
      ( ~ v1_funct_2(u1_waybel_0(A_320,B_321),u1_struct_0(B_321),u1_struct_0(A_320))
      | ~ v1_funct_1(u1_waybel_0(A_320,B_321))
      | v1_xboole_0(u1_struct_0(A_320))
      | v1_xboole_0(u1_struct_0(B_321))
      | r1_waybel_0(A_320,B_321,k2_relset_1(u1_struct_0(B_321),u1_struct_0(A_320),u1_waybel_0(A_320,B_321)))
      | v2_struct_0(A_320)
      | ~ l1_waybel_0(B_321,A_320)
      | ~ l1_struct_0(A_320)
      | ~ l1_waybel_0(B_321,A_322)
      | v2_struct_0(B_321)
      | ~ l1_struct_0(A_322)
      | v2_struct_0(A_322) ) ),
    inference(resolution,[status(thm)],[c_58,c_295])).

tff(c_321,plain,(
    ! [A_320] :
      ( ~ v1_funct_2(u1_waybel_0(A_320,'#skF_8'),u1_struct_0('#skF_8'),u1_struct_0(A_320))
      | ~ v1_funct_1(u1_waybel_0(A_320,'#skF_8'))
      | v1_xboole_0(u1_struct_0(A_320))
      | v1_xboole_0(u1_struct_0('#skF_8'))
      | r1_waybel_0(A_320,'#skF_8',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0(A_320),u1_waybel_0(A_320,'#skF_8')))
      | v2_struct_0(A_320)
      | ~ l1_waybel_0('#skF_8',A_320)
      | ~ l1_struct_0(A_320)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_317])).

tff(c_325,plain,(
    ! [A_320] :
      ( ~ v1_funct_2(u1_waybel_0(A_320,'#skF_8'),u1_struct_0('#skF_8'),u1_struct_0(A_320))
      | ~ v1_funct_1(u1_waybel_0(A_320,'#skF_8'))
      | v1_xboole_0(u1_struct_0(A_320))
      | v1_xboole_0(u1_struct_0('#skF_8'))
      | r1_waybel_0(A_320,'#skF_8',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0(A_320),u1_waybel_0(A_320,'#skF_8')))
      | v2_struct_0(A_320)
      | ~ l1_waybel_0('#skF_8',A_320)
      | ~ l1_struct_0(A_320)
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_321])).

tff(c_326,plain,(
    ! [A_320] :
      ( ~ v1_funct_2(u1_waybel_0(A_320,'#skF_8'),u1_struct_0('#skF_8'),u1_struct_0(A_320))
      | ~ v1_funct_1(u1_waybel_0(A_320,'#skF_8'))
      | v1_xboole_0(u1_struct_0(A_320))
      | v1_xboole_0(u1_struct_0('#skF_8'))
      | r1_waybel_0(A_320,'#skF_8',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0(A_320),u1_waybel_0(A_320,'#skF_8')))
      | v2_struct_0(A_320)
      | ~ l1_waybel_0('#skF_8',A_320)
      | ~ l1_struct_0(A_320) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_325])).

tff(c_327,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_46,plain,(
    ! [A_139] :
      ( v4_orders_2('#skF_6'(A_139))
      | ~ l1_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_40,plain,(
    ! [A_139] :
      ( v7_waybel_0('#skF_6'(A_139))
      | ~ l1_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    ! [A_139] :
      ( l1_waybel_0('#skF_6'(A_139),A_139)
      | ~ l1_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_56,plain,(
    ! [A_148,B_150] :
      ( r1_waybel_0(A_148,B_150,u1_struct_0(A_148))
      | ~ l1_waybel_0(B_150,A_148)
      | ~ v7_waybel_0(B_150)
      | ~ v4_orders_2(B_150)
      | v2_struct_0(B_150)
      | ~ l1_struct_0(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_54,plain,(
    ! [A_141,B_145,C_147] :
      ( r2_waybel_0(A_141,B_145,C_147)
      | ~ r1_waybel_0(A_141,B_145,C_147)
      | ~ l1_waybel_0(B_145,A_141)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_117,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( r2_hidden(k2_waybel_0(A_210,B_211,'#skF_5'(A_210,B_211,C_212,D_213)),C_212)
      | ~ m1_subset_1(D_213,u1_struct_0(B_211))
      | ~ r2_waybel_0(A_210,B_211,C_212)
      | ~ l1_waybel_0(B_211,A_210)
      | v2_struct_0(B_211)
      | ~ l1_struct_0(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [C_214,D_215,B_216,A_217] :
      ( ~ v1_xboole_0(C_214)
      | ~ m1_subset_1(D_215,u1_struct_0(B_216))
      | ~ r2_waybel_0(A_217,B_216,C_214)
      | ~ l1_waybel_0(B_216,A_217)
      | v2_struct_0(B_216)
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_138,plain,(
    ! [C_218,A_219,B_220,A_221] :
      ( ~ v1_xboole_0(C_218)
      | ~ r2_waybel_0(A_219,B_220,C_218)
      | ~ l1_waybel_0(B_220,A_219)
      | ~ l1_struct_0(A_219)
      | v2_struct_0(A_219)
      | ~ l1_waybel_0(B_220,A_221)
      | v2_struct_0(B_220)
      | ~ l1_struct_0(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_165,plain,(
    ! [C_234,B_235,A_236,A_237] :
      ( ~ v1_xboole_0(C_234)
      | ~ l1_waybel_0(B_235,A_236)
      | ~ l1_struct_0(A_236)
      | v2_struct_0(A_236)
      | ~ r1_waybel_0(A_237,B_235,C_234)
      | ~ l1_waybel_0(B_235,A_237)
      | ~ v7_waybel_0(B_235)
      | ~ v4_orders_2(B_235)
      | v2_struct_0(B_235)
      | ~ l1_struct_0(A_237)
      | v2_struct_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_54,c_138])).

tff(c_176,plain,(
    ! [C_238,A_239,A_240] :
      ( ~ v1_xboole_0(C_238)
      | v2_struct_0(A_239)
      | ~ r1_waybel_0(A_240,'#skF_6'(A_239),C_238)
      | ~ l1_waybel_0('#skF_6'(A_239),A_240)
      | ~ v7_waybel_0('#skF_6'(A_239))
      | ~ v4_orders_2('#skF_6'(A_239))
      | v2_struct_0('#skF_6'(A_239))
      | ~ l1_struct_0(A_240)
      | v2_struct_0(A_240)
      | ~ l1_struct_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_52,c_165])).

tff(c_182,plain,(
    ! [A_241,A_242] :
      ( ~ v1_xboole_0(u1_struct_0(A_241))
      | v2_struct_0(A_242)
      | ~ l1_struct_0(A_242)
      | ~ l1_waybel_0('#skF_6'(A_242),A_241)
      | ~ v7_waybel_0('#skF_6'(A_242))
      | ~ v4_orders_2('#skF_6'(A_242))
      | v2_struct_0('#skF_6'(A_242))
      | ~ l1_struct_0(A_241)
      | v2_struct_0(A_241) ) ),
    inference(resolution,[status(thm)],[c_56,c_176])).

tff(c_198,plain,(
    ! [A_247] :
      ( ~ v1_xboole_0(u1_struct_0(A_247))
      | ~ v7_waybel_0('#skF_6'(A_247))
      | ~ v4_orders_2('#skF_6'(A_247))
      | v2_struct_0('#skF_6'(A_247))
      | v2_struct_0(A_247)
      | ~ l1_struct_0(A_247) ) ),
    inference(resolution,[status(thm)],[c_52,c_182])).

tff(c_203,plain,(
    ! [A_248] :
      ( ~ v1_xboole_0(u1_struct_0(A_248))
      | ~ v4_orders_2('#skF_6'(A_248))
      | v2_struct_0('#skF_6'(A_248))
      | v2_struct_0(A_248)
      | ~ l1_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_40,c_198])).

tff(c_208,plain,(
    ! [A_249] :
      ( ~ v1_xboole_0(u1_struct_0(A_249))
      | v2_struct_0('#skF_6'(A_249))
      | v2_struct_0(A_249)
      | ~ l1_struct_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_46,c_203])).

tff(c_50,plain,(
    ! [A_139] :
      ( ~ v2_struct_0('#skF_6'(A_139))
      | ~ l1_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_212,plain,(
    ! [A_249] :
      ( ~ v1_xboole_0(u1_struct_0(A_249))
      | v2_struct_0(A_249)
      | ~ l1_struct_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_208,c_50])).

tff(c_330,plain,
    ( v2_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_327,c_212])).

tff(c_333,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_330])).

tff(c_336,plain,(
    ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_333])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_336])).

tff(c_343,plain,(
    ! [A_323] :
      ( ~ v1_funct_2(u1_waybel_0(A_323,'#skF_8'),u1_struct_0('#skF_8'),u1_struct_0(A_323))
      | ~ v1_funct_1(u1_waybel_0(A_323,'#skF_8'))
      | v1_xboole_0(u1_struct_0(A_323))
      | r1_waybel_0(A_323,'#skF_8',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0(A_323),u1_waybel_0(A_323,'#skF_8')))
      | v2_struct_0(A_323)
      | ~ l1_waybel_0('#skF_8',A_323)
      | ~ l1_struct_0(A_323) ) ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_60,plain,(
    ~ r1_waybel_0('#skF_7','#skF_8',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),u1_waybel_0('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_348,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1(u1_waybel_0('#skF_7','#skF_8'))
    | v1_xboole_0(u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7')
    | ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_343,c_60])).

tff(c_354,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1(u1_waybel_0('#skF_7','#skF_8'))
    | v1_xboole_0(u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_348])).

tff(c_355,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1(u1_waybel_0('#skF_7','#skF_8'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_354])).

tff(c_356,plain,(
    ~ v1_funct_1(u1_waybel_0('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_359,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_356])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_359])).

tff(c_364,plain,
    ( ~ v1_funct_2(u1_waybel_0('#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_372,plain,(
    ~ v1_funct_2(u1_waybel_0('#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_375,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_372])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_375])).

tff(c_380,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_384,plain,
    ( v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_380,c_212])).

tff(c_387,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_384])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.49  
% 3.30/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.49  %$ v1_funct_2 > r2_waybel_0 > r1_waybel_0 > r1_orders_2 > v6_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_waybel_0 > k2_relset_1 > u1_waybel_0 > o_2_4_waybel_9 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_6
% 3.30/1.49  
% 3.30/1.49  %Foreground sorts:
% 3.30/1.49  
% 3.30/1.49  
% 3.30/1.49  %Background operators:
% 3.30/1.49  
% 3.30/1.49  
% 3.30/1.49  %Foreground operators:
% 3.30/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.30/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.30/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.30/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.49  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 3.30/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.49  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.30/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.30/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.30/1.49  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 3.30/1.49  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.30/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.30/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.30/1.49  tff(o_2_4_waybel_9, type, o_2_4_waybel_9: ($i * $i) > $i).
% 3.30/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.49  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.30/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.30/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.30/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.30/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.30/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.30/1.49  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 3.30/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.30/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.49  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.30/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.30/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.30/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.49  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.30/1.49  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.30/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.49  
% 3.30/1.51  tff(f_216, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 3.30/1.51  tff(f_135, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 3.30/1.51  tff(f_125, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 3.30/1.51  tff(f_54, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.30/1.51  tff(f_202, axiom, (![A, B]: ((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_4_waybel_9(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_4_waybel_9)).
% 3.30/1.51  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 3.30/1.51  tff(f_118, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k3_funct_2(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_waybel_0)).
% 3.30/1.51  tff(f_50, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 3.30/1.51  tff(f_153, axiom, (![A]: (l1_struct_0(A) => (?[B]: ((((((l1_waybel_0(B, A) & ~v2_struct_0(B)) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & v6_waybel_0(B, A)) & v7_waybel_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc5_waybel_0)).
% 3.30/1.51  tff(f_190, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 3.30/1.51  tff(f_173, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) => r2_waybel_0(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_yellow_6)).
% 3.30/1.51  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 3.30/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.30/1.51  tff(c_68, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.30/1.51  tff(c_66, plain, (l1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.30/1.51  tff(c_62, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.30/1.51  tff(c_36, plain, (![A_137, B_138]: (v1_funct_2(u1_waybel_0(A_137, B_138), u1_struct_0(B_138), u1_struct_0(A_137)) | ~l1_waybel_0(B_138, A_137) | ~l1_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.30/1.51  tff(c_38, plain, (![A_137, B_138]: (v1_funct_1(u1_waybel_0(A_137, B_138)) | ~l1_waybel_0(B_138, A_137) | ~l1_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.30/1.51  tff(c_83, plain, (![B_165, A_166]: (l1_orders_2(B_165) | ~l1_waybel_0(B_165, A_166) | ~l1_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.30/1.51  tff(c_89, plain, (l1_orders_2('#skF_8') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_62, c_83])).
% 3.30/1.51  tff(c_93, plain, (l1_orders_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_89])).
% 3.30/1.51  tff(c_8, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.30/1.51  tff(c_64, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.30/1.51  tff(c_58, plain, (![A_151, B_152]: (m1_subset_1(o_2_4_waybel_9(A_151, B_152), u1_struct_0(B_152)) | ~l1_waybel_0(B_152, A_151) | v2_struct_0(B_152) | ~l1_struct_0(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.30/1.51  tff(c_34, plain, (![A_137, B_138]: (m1_subset_1(u1_waybel_0(A_137, B_138), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_138), u1_struct_0(A_137)))) | ~l1_waybel_0(B_138, A_137) | ~l1_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.30/1.51  tff(c_18, plain, (![A_21, B_49, C_63, D_70]: (m1_subset_1('#skF_2'(A_21, B_49, C_63, D_70), u1_struct_0(B_49)) | r1_waybel_0(A_21, B_49, C_63) | ~m1_subset_1(D_70, u1_struct_0(B_49)) | ~l1_waybel_0(B_49, A_21) | v2_struct_0(B_49) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.30/1.51  tff(c_30, plain, (![B_131, A_127, C_133]: (k3_funct_2(u1_struct_0(B_131), u1_struct_0(A_127), u1_waybel_0(A_127, B_131), C_133)=k2_waybel_0(A_127, B_131, C_133) | ~m1_subset_1(C_133, u1_struct_0(B_131)) | ~l1_waybel_0(B_131, A_127) | v2_struct_0(B_131) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.30/1.51  tff(c_142, plain, (![A_222, B_223, D_224, C_225]: (r2_hidden(k3_funct_2(A_222, B_223, D_224, C_225), k2_relset_1(A_222, B_223, D_224)) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_2(D_224, A_222, B_223) | ~v1_funct_1(D_224) | ~m1_subset_1(C_225, A_222) | v1_xboole_0(B_223) | v1_xboole_0(A_222))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.51  tff(c_265, plain, (![A_304, B_305, C_306]: (r2_hidden(k2_waybel_0(A_304, B_305, C_306), k2_relset_1(u1_struct_0(B_305), u1_struct_0(A_304), u1_waybel_0(A_304, B_305))) | ~m1_subset_1(u1_waybel_0(A_304, B_305), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_305), u1_struct_0(A_304)))) | ~v1_funct_2(u1_waybel_0(A_304, B_305), u1_struct_0(B_305), u1_struct_0(A_304)) | ~v1_funct_1(u1_waybel_0(A_304, B_305)) | ~m1_subset_1(C_306, u1_struct_0(B_305)) | v1_xboole_0(u1_struct_0(A_304)) | v1_xboole_0(u1_struct_0(B_305)) | ~m1_subset_1(C_306, u1_struct_0(B_305)) | ~l1_waybel_0(B_305, A_304) | v2_struct_0(B_305) | ~l1_struct_0(A_304) | v2_struct_0(A_304))), inference(superposition, [status(thm), theory('equality')], [c_30, c_142])).
% 3.30/1.51  tff(c_14, plain, (![A_21, B_49, C_63, D_70]: (~r2_hidden(k2_waybel_0(A_21, B_49, '#skF_2'(A_21, B_49, C_63, D_70)), C_63) | r1_waybel_0(A_21, B_49, C_63) | ~m1_subset_1(D_70, u1_struct_0(B_49)) | ~l1_waybel_0(B_49, A_21) | v2_struct_0(B_49) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.30/1.51  tff(c_285, plain, (![A_307, B_308, D_309]: (r1_waybel_0(A_307, B_308, k2_relset_1(u1_struct_0(B_308), u1_struct_0(A_307), u1_waybel_0(A_307, B_308))) | ~m1_subset_1(D_309, u1_struct_0(B_308)) | ~m1_subset_1(u1_waybel_0(A_307, B_308), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_308), u1_struct_0(A_307)))) | ~v1_funct_2(u1_waybel_0(A_307, B_308), u1_struct_0(B_308), u1_struct_0(A_307)) | ~v1_funct_1(u1_waybel_0(A_307, B_308)) | v1_xboole_0(u1_struct_0(A_307)) | v1_xboole_0(u1_struct_0(B_308)) | ~m1_subset_1('#skF_2'(A_307, B_308, k2_relset_1(u1_struct_0(B_308), u1_struct_0(A_307), u1_waybel_0(A_307, B_308)), D_309), u1_struct_0(B_308)) | ~l1_waybel_0(B_308, A_307) | v2_struct_0(B_308) | ~l1_struct_0(A_307) | v2_struct_0(A_307))), inference(resolution, [status(thm)], [c_265, c_14])).
% 3.30/1.51  tff(c_291, plain, (![A_310, B_311, D_312]: (~m1_subset_1(u1_waybel_0(A_310, B_311), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_311), u1_struct_0(A_310)))) | ~v1_funct_2(u1_waybel_0(A_310, B_311), u1_struct_0(B_311), u1_struct_0(A_310)) | ~v1_funct_1(u1_waybel_0(A_310, B_311)) | v1_xboole_0(u1_struct_0(A_310)) | v1_xboole_0(u1_struct_0(B_311)) | r1_waybel_0(A_310, B_311, k2_relset_1(u1_struct_0(B_311), u1_struct_0(A_310), u1_waybel_0(A_310, B_311))) | ~m1_subset_1(D_312, u1_struct_0(B_311)) | ~l1_waybel_0(B_311, A_310) | v2_struct_0(B_311) | ~l1_struct_0(A_310) | v2_struct_0(A_310))), inference(resolution, [status(thm)], [c_18, c_285])).
% 3.30/1.51  tff(c_295, plain, (![A_313, B_314, D_315]: (~v1_funct_2(u1_waybel_0(A_313, B_314), u1_struct_0(B_314), u1_struct_0(A_313)) | ~v1_funct_1(u1_waybel_0(A_313, B_314)) | v1_xboole_0(u1_struct_0(A_313)) | v1_xboole_0(u1_struct_0(B_314)) | r1_waybel_0(A_313, B_314, k2_relset_1(u1_struct_0(B_314), u1_struct_0(A_313), u1_waybel_0(A_313, B_314))) | ~m1_subset_1(D_315, u1_struct_0(B_314)) | v2_struct_0(B_314) | v2_struct_0(A_313) | ~l1_waybel_0(B_314, A_313) | ~l1_struct_0(A_313))), inference(resolution, [status(thm)], [c_34, c_291])).
% 3.30/1.51  tff(c_317, plain, (![A_320, B_321, A_322]: (~v1_funct_2(u1_waybel_0(A_320, B_321), u1_struct_0(B_321), u1_struct_0(A_320)) | ~v1_funct_1(u1_waybel_0(A_320, B_321)) | v1_xboole_0(u1_struct_0(A_320)) | v1_xboole_0(u1_struct_0(B_321)) | r1_waybel_0(A_320, B_321, k2_relset_1(u1_struct_0(B_321), u1_struct_0(A_320), u1_waybel_0(A_320, B_321))) | v2_struct_0(A_320) | ~l1_waybel_0(B_321, A_320) | ~l1_struct_0(A_320) | ~l1_waybel_0(B_321, A_322) | v2_struct_0(B_321) | ~l1_struct_0(A_322) | v2_struct_0(A_322))), inference(resolution, [status(thm)], [c_58, c_295])).
% 3.30/1.51  tff(c_321, plain, (![A_320]: (~v1_funct_2(u1_waybel_0(A_320, '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0(A_320)) | ~v1_funct_1(u1_waybel_0(A_320, '#skF_8')) | v1_xboole_0(u1_struct_0(A_320)) | v1_xboole_0(u1_struct_0('#skF_8')) | r1_waybel_0(A_320, '#skF_8', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0(A_320), u1_waybel_0(A_320, '#skF_8'))) | v2_struct_0(A_320) | ~l1_waybel_0('#skF_8', A_320) | ~l1_struct_0(A_320) | v2_struct_0('#skF_8') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_317])).
% 3.30/1.51  tff(c_325, plain, (![A_320]: (~v1_funct_2(u1_waybel_0(A_320, '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0(A_320)) | ~v1_funct_1(u1_waybel_0(A_320, '#skF_8')) | v1_xboole_0(u1_struct_0(A_320)) | v1_xboole_0(u1_struct_0('#skF_8')) | r1_waybel_0(A_320, '#skF_8', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0(A_320), u1_waybel_0(A_320, '#skF_8'))) | v2_struct_0(A_320) | ~l1_waybel_0('#skF_8', A_320) | ~l1_struct_0(A_320) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_321])).
% 3.30/1.51  tff(c_326, plain, (![A_320]: (~v1_funct_2(u1_waybel_0(A_320, '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0(A_320)) | ~v1_funct_1(u1_waybel_0(A_320, '#skF_8')) | v1_xboole_0(u1_struct_0(A_320)) | v1_xboole_0(u1_struct_0('#skF_8')) | r1_waybel_0(A_320, '#skF_8', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0(A_320), u1_waybel_0(A_320, '#skF_8'))) | v2_struct_0(A_320) | ~l1_waybel_0('#skF_8', A_320) | ~l1_struct_0(A_320))), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_325])).
% 3.30/1.51  tff(c_327, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_326])).
% 3.30/1.51  tff(c_46, plain, (![A_139]: (v4_orders_2('#skF_6'(A_139)) | ~l1_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.30/1.51  tff(c_40, plain, (![A_139]: (v7_waybel_0('#skF_6'(A_139)) | ~l1_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.30/1.51  tff(c_52, plain, (![A_139]: (l1_waybel_0('#skF_6'(A_139), A_139) | ~l1_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.30/1.51  tff(c_56, plain, (![A_148, B_150]: (r1_waybel_0(A_148, B_150, u1_struct_0(A_148)) | ~l1_waybel_0(B_150, A_148) | ~v7_waybel_0(B_150) | ~v4_orders_2(B_150) | v2_struct_0(B_150) | ~l1_struct_0(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.30/1.51  tff(c_54, plain, (![A_141, B_145, C_147]: (r2_waybel_0(A_141, B_145, C_147) | ~r1_waybel_0(A_141, B_145, C_147) | ~l1_waybel_0(B_145, A_141) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.30/1.51  tff(c_117, plain, (![A_210, B_211, C_212, D_213]: (r2_hidden(k2_waybel_0(A_210, B_211, '#skF_5'(A_210, B_211, C_212, D_213)), C_212) | ~m1_subset_1(D_213, u1_struct_0(B_211)) | ~r2_waybel_0(A_210, B_211, C_212) | ~l1_waybel_0(B_211, A_210) | v2_struct_0(B_211) | ~l1_struct_0(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.51  tff(c_122, plain, (![C_214, D_215, B_216, A_217]: (~v1_xboole_0(C_214) | ~m1_subset_1(D_215, u1_struct_0(B_216)) | ~r2_waybel_0(A_217, B_216, C_214) | ~l1_waybel_0(B_216, A_217) | v2_struct_0(B_216) | ~l1_struct_0(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_117, c_2])).
% 3.30/1.51  tff(c_138, plain, (![C_218, A_219, B_220, A_221]: (~v1_xboole_0(C_218) | ~r2_waybel_0(A_219, B_220, C_218) | ~l1_waybel_0(B_220, A_219) | ~l1_struct_0(A_219) | v2_struct_0(A_219) | ~l1_waybel_0(B_220, A_221) | v2_struct_0(B_220) | ~l1_struct_0(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_58, c_122])).
% 3.30/1.51  tff(c_165, plain, (![C_234, B_235, A_236, A_237]: (~v1_xboole_0(C_234) | ~l1_waybel_0(B_235, A_236) | ~l1_struct_0(A_236) | v2_struct_0(A_236) | ~r1_waybel_0(A_237, B_235, C_234) | ~l1_waybel_0(B_235, A_237) | ~v7_waybel_0(B_235) | ~v4_orders_2(B_235) | v2_struct_0(B_235) | ~l1_struct_0(A_237) | v2_struct_0(A_237))), inference(resolution, [status(thm)], [c_54, c_138])).
% 3.30/1.51  tff(c_176, plain, (![C_238, A_239, A_240]: (~v1_xboole_0(C_238) | v2_struct_0(A_239) | ~r1_waybel_0(A_240, '#skF_6'(A_239), C_238) | ~l1_waybel_0('#skF_6'(A_239), A_240) | ~v7_waybel_0('#skF_6'(A_239)) | ~v4_orders_2('#skF_6'(A_239)) | v2_struct_0('#skF_6'(A_239)) | ~l1_struct_0(A_240) | v2_struct_0(A_240) | ~l1_struct_0(A_239))), inference(resolution, [status(thm)], [c_52, c_165])).
% 3.30/1.51  tff(c_182, plain, (![A_241, A_242]: (~v1_xboole_0(u1_struct_0(A_241)) | v2_struct_0(A_242) | ~l1_struct_0(A_242) | ~l1_waybel_0('#skF_6'(A_242), A_241) | ~v7_waybel_0('#skF_6'(A_242)) | ~v4_orders_2('#skF_6'(A_242)) | v2_struct_0('#skF_6'(A_242)) | ~l1_struct_0(A_241) | v2_struct_0(A_241))), inference(resolution, [status(thm)], [c_56, c_176])).
% 3.30/1.51  tff(c_198, plain, (![A_247]: (~v1_xboole_0(u1_struct_0(A_247)) | ~v7_waybel_0('#skF_6'(A_247)) | ~v4_orders_2('#skF_6'(A_247)) | v2_struct_0('#skF_6'(A_247)) | v2_struct_0(A_247) | ~l1_struct_0(A_247))), inference(resolution, [status(thm)], [c_52, c_182])).
% 3.30/1.51  tff(c_203, plain, (![A_248]: (~v1_xboole_0(u1_struct_0(A_248)) | ~v4_orders_2('#skF_6'(A_248)) | v2_struct_0('#skF_6'(A_248)) | v2_struct_0(A_248) | ~l1_struct_0(A_248))), inference(resolution, [status(thm)], [c_40, c_198])).
% 3.30/1.51  tff(c_208, plain, (![A_249]: (~v1_xboole_0(u1_struct_0(A_249)) | v2_struct_0('#skF_6'(A_249)) | v2_struct_0(A_249) | ~l1_struct_0(A_249))), inference(resolution, [status(thm)], [c_46, c_203])).
% 3.30/1.51  tff(c_50, plain, (![A_139]: (~v2_struct_0('#skF_6'(A_139)) | ~l1_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.30/1.51  tff(c_212, plain, (![A_249]: (~v1_xboole_0(u1_struct_0(A_249)) | v2_struct_0(A_249) | ~l1_struct_0(A_249))), inference(resolution, [status(thm)], [c_208, c_50])).
% 3.30/1.51  tff(c_330, plain, (v2_struct_0('#skF_8') | ~l1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_327, c_212])).
% 3.30/1.51  tff(c_333, plain, (~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_330])).
% 3.30/1.51  tff(c_336, plain, (~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_8, c_333])).
% 3.30/1.51  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_336])).
% 3.30/1.51  tff(c_343, plain, (![A_323]: (~v1_funct_2(u1_waybel_0(A_323, '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0(A_323)) | ~v1_funct_1(u1_waybel_0(A_323, '#skF_8')) | v1_xboole_0(u1_struct_0(A_323)) | r1_waybel_0(A_323, '#skF_8', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0(A_323), u1_waybel_0(A_323, '#skF_8'))) | v2_struct_0(A_323) | ~l1_waybel_0('#skF_8', A_323) | ~l1_struct_0(A_323))), inference(splitRight, [status(thm)], [c_326])).
% 3.30/1.51  tff(c_60, plain, (~r1_waybel_0('#skF_7', '#skF_8', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), u1_waybel_0('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.30/1.51  tff(c_348, plain, (~v1_funct_2(u1_waybel_0('#skF_7', '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1(u1_waybel_0('#skF_7', '#skF_8')) | v1_xboole_0(u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_343, c_60])).
% 3.30/1.51  tff(c_354, plain, (~v1_funct_2(u1_waybel_0('#skF_7', '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1(u1_waybel_0('#skF_7', '#skF_8')) | v1_xboole_0(u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_348])).
% 3.30/1.51  tff(c_355, plain, (~v1_funct_2(u1_waybel_0('#skF_7', '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1(u1_waybel_0('#skF_7', '#skF_8')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_68, c_354])).
% 3.30/1.51  tff(c_356, plain, (~v1_funct_1(u1_waybel_0('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_355])).
% 3.30/1.51  tff(c_359, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_356])).
% 3.30/1.51  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_359])).
% 3.30/1.51  tff(c_364, plain, (~v1_funct_2(u1_waybel_0('#skF_7', '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_355])).
% 3.30/1.51  tff(c_372, plain, (~v1_funct_2(u1_waybel_0('#skF_7', '#skF_8'), u1_struct_0('#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_364])).
% 3.30/1.51  tff(c_375, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_372])).
% 3.30/1.51  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_375])).
% 3.30/1.51  tff(c_380, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_364])).
% 3.30/1.51  tff(c_384, plain, (v2_struct_0('#skF_7') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_380, c_212])).
% 3.30/1.51  tff(c_387, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_384])).
% 3.30/1.51  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_387])).
% 3.30/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  
% 3.30/1.51  Inference rules
% 3.30/1.51  ----------------------
% 3.30/1.51  #Ref     : 0
% 3.30/1.51  #Sup     : 58
% 3.30/1.51  #Fact    : 0
% 3.30/1.51  #Define  : 0
% 3.30/1.51  #Split   : 4
% 3.30/1.51  #Chain   : 0
% 3.30/1.51  #Close   : 0
% 3.30/1.51  
% 3.30/1.51  Ordering : KBO
% 3.30/1.51  
% 3.30/1.51  Simplification rules
% 3.30/1.51  ----------------------
% 3.30/1.51  #Subsume      : 19
% 3.30/1.51  #Demod        : 11
% 3.30/1.51  #Tautology    : 5
% 3.30/1.51  #SimpNegUnit  : 6
% 3.30/1.51  #BackRed      : 0
% 3.30/1.51  
% 3.30/1.51  #Partial instantiations: 0
% 3.30/1.51  #Strategies tried      : 1
% 3.30/1.51  
% 3.30/1.51  Timing (in seconds)
% 3.30/1.51  ----------------------
% 3.30/1.51  Preprocessing        : 0.37
% 3.30/1.51  Parsing              : 0.20
% 3.30/1.51  CNF conversion       : 0.04
% 3.30/1.51  Main loop            : 0.37
% 3.30/1.51  Inferencing          : 0.16
% 3.30/1.51  Reduction            : 0.08
% 3.30/1.51  Demodulation         : 0.05
% 3.30/1.51  BG Simplification    : 0.02
% 3.30/1.51  Subsumption          : 0.08
% 3.30/1.52  Abstraction          : 0.01
% 3.30/1.52  MUC search           : 0.00
% 3.30/1.52  Cooper               : 0.00
% 3.30/1.52  Total                : 0.78
% 3.30/1.52  Index Insertion      : 0.00
% 3.30/1.52  Index Deletion       : 0.00
% 3.30/1.52  Index Matching       : 0.00
% 3.30/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
