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
% DateTime   : Thu Dec  3 10:31:05 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 591 expanded)
%              Number of leaves         :   44 ( 238 expanded)
%              Depth                    :   21
%              Number of atoms          :  428 (2965 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v5_waybel_6,type,(
    v5_waybel_6: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_waybel_7,type,(
    v4_waybel_7: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_237,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v5_waybel_6(B,A)
             => v4_waybel_7(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v12_waybel_0(k5_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

tff(f_217,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v5_waybel_6(B,A)
           => v1_waybel_7(k5_waybel_0(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

tff(f_152,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k5_waybel_0(A,B))
        & v1_waybel_0(k5_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_198,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v4_waybel_7(B,A)
          <=> ? [C] :
                ( ~ v1_xboole_0(C)
                & v1_waybel_0(C,A)
                & v12_waybel_0(C,A)
                & v1_waybel_7(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                & B = k1_yellow_0(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

tff(c_72,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_76,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_82,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_118,plain,(
    ! [A_102,B_103,C_104] :
      ( r3_orders_2(A_102,B_103,B_103)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_124,plain,(
    ! [B_103] :
      ( r3_orders_2('#skF_4',B_103,B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_118])).

tff(c_129,plain,(
    ! [B_103] :
      ( r3_orders_2('#skF_4',B_103,B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_72,c_124])).

tff(c_130,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v2_struct_0(A_10)
      | ~ v1_lattice3(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_137,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_10])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_137])).

tff(c_143,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_80,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( v12_waybel_0(k5_waybel_0(A_49,B_50),A_49)
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_78,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_74,plain,(
    v2_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_68,plain,(
    v5_waybel_6('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_64,plain,(
    ! [A_70,B_72] :
      ( v1_waybel_7(k5_waybel_0(A_70,B_72),A_70)
      | ~ v5_waybel_6(B_72,A_70)
      | ~ m1_subset_1(B_72,u1_struct_0(A_70))
      | ~ l1_orders_2(A_70)
      | ~ v2_lattice3(A_70)
      | ~ v1_lattice3(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_42,plain,(
    ! [A_51,B_52] :
      ( v1_waybel_0(k5_waybel_0(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l1_orders_2(A_51)
      | ~ v3_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_86,plain,(
    ! [A_80,B_81] :
      ( ~ v1_xboole_0(k5_waybel_0(A_80,B_81))
      | ~ m1_subset_1(B_81,u1_struct_0(A_80))
      | ~ l1_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_92,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_86])).

tff(c_96,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_72,c_92])).

tff(c_97,plain,(
    ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_66,plain,(
    ~ v4_waybel_7('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_144,plain,(
    ! [B_107] :
      ( r3_orders_2('#skF_4',B_107,B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_159,plain,(
    r3_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_144])).

tff(c_205,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_orders_2(A_135,B_136,C_137)
      | ~ r3_orders_2(A_135,B_136,C_137)
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_213,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_205])).

tff(c_225,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_72,c_70,c_213])).

tff(c_226,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_225])).

tff(c_18,plain,(
    ! [A_11,B_18,C_19] :
      ( m1_subset_1('#skF_1'(A_11,B_18,C_19),u1_struct_0(A_11))
      | r2_lattice3(A_11,B_18,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_11,B_18,C_19] :
      ( r2_hidden('#skF_1'(A_11,B_18,C_19),B_18)
      | r2_lattice3(A_11,B_18,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_186,plain,(
    ! [A_122,C_123,B_124] :
      ( r1_orders_2(A_122,C_123,B_124)
      | ~ r2_hidden(C_123,k5_waybel_0(A_122,B_124))
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1(B_124,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_990,plain,(
    ! [A_313,A_314,B_315,C_316] :
      ( r1_orders_2(A_313,'#skF_1'(A_314,k5_waybel_0(A_313,B_315),C_316),B_315)
      | ~ m1_subset_1('#skF_1'(A_314,k5_waybel_0(A_313,B_315),C_316),u1_struct_0(A_313))
      | ~ m1_subset_1(B_315,u1_struct_0(A_313))
      | ~ l1_orders_2(A_313)
      | v2_struct_0(A_313)
      | r2_lattice3(A_314,k5_waybel_0(A_313,B_315),C_316)
      | ~ m1_subset_1(C_316,u1_struct_0(A_314))
      | ~ l1_orders_2(A_314) ) ),
    inference(resolution,[status(thm)],[c_16,c_186])).

tff(c_999,plain,(
    ! [A_320,B_321,C_322] :
      ( r1_orders_2(A_320,'#skF_1'(A_320,k5_waybel_0(A_320,B_321),C_322),B_321)
      | ~ m1_subset_1(B_321,u1_struct_0(A_320))
      | v2_struct_0(A_320)
      | r2_lattice3(A_320,k5_waybel_0(A_320,B_321),C_322)
      | ~ m1_subset_1(C_322,u1_struct_0(A_320))
      | ~ l1_orders_2(A_320) ) ),
    inference(resolution,[status(thm)],[c_18,c_990])).

tff(c_14,plain,(
    ! [A_11,B_18,C_19] :
      ( ~ r1_orders_2(A_11,'#skF_1'(A_11,B_18,C_19),C_19)
      | r2_lattice3(A_11,B_18,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1004,plain,(
    ! [A_320,B_321] :
      ( v2_struct_0(A_320)
      | r2_lattice3(A_320,k5_waybel_0(A_320,B_321),B_321)
      | ~ m1_subset_1(B_321,u1_struct_0(A_320))
      | ~ l1_orders_2(A_320) ) ),
    inference(resolution,[status(thm)],[c_999,c_14])).

tff(c_36,plain,(
    ! [A_25,B_37,C_43] :
      ( m1_subset_1('#skF_2'(A_25,B_37,C_43),u1_struct_0(A_25))
      | k1_yellow_0(A_25,C_43) = B_37
      | ~ r2_lattice3(A_25,C_43,B_37)
      | ~ m1_subset_1(B_37,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v5_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    ! [A_25,C_43,B_37] :
      ( r2_lattice3(A_25,C_43,'#skF_2'(A_25,B_37,C_43))
      | k1_yellow_0(A_25,C_43) = B_37
      | ~ r2_lattice3(A_25,C_43,B_37)
      | ~ m1_subset_1(B_37,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v5_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    ! [C_59,A_53,B_57] :
      ( r2_hidden(C_59,k5_waybel_0(A_53,B_57))
      | ~ r1_orders_2(A_53,C_59,B_57)
      | ~ m1_subset_1(C_59,u1_struct_0(A_53))
      | ~ m1_subset_1(B_57,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_196,plain,(
    ! [A_125,D_126,C_127,B_128] :
      ( r1_orders_2(A_125,D_126,C_127)
      | ~ r2_hidden(D_126,B_128)
      | ~ m1_subset_1(D_126,u1_struct_0(A_125))
      | ~ r2_lattice3(A_125,B_128,C_127)
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_897,plain,(
    ! [B_274,C_277,C_275,A_276,A_273] :
      ( r1_orders_2(A_276,C_277,C_275)
      | ~ m1_subset_1(C_277,u1_struct_0(A_276))
      | ~ r2_lattice3(A_276,k5_waybel_0(A_273,B_274),C_275)
      | ~ m1_subset_1(C_275,u1_struct_0(A_276))
      | ~ l1_orders_2(A_276)
      | ~ r1_orders_2(A_273,C_277,B_274)
      | ~ m1_subset_1(C_277,u1_struct_0(A_273))
      | ~ m1_subset_1(B_274,u1_struct_0(A_273))
      | ~ l1_orders_2(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_46,c_196])).

tff(c_909,plain,(
    ! [C_275,A_273,B_274] :
      ( r1_orders_2('#skF_4','#skF_5',C_275)
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_273,B_274),C_275)
      | ~ m1_subset_1(C_275,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r1_orders_2(A_273,'#skF_5',B_274)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_273))
      | ~ m1_subset_1(B_274,u1_struct_0(A_273))
      | ~ l1_orders_2(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_70,c_897])).

tff(c_918,plain,(
    ! [C_278,A_279,B_280] :
      ( r1_orders_2('#skF_4','#skF_5',C_278)
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_279,B_280),C_278)
      | ~ m1_subset_1(C_278,u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_279,'#skF_5',B_280)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_279))
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | v2_struct_0(A_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_909])).

tff(c_922,plain,(
    ! [B_37,A_279,B_280] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_37,k5_waybel_0(A_279,B_280)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_37,k5_waybel_0(A_279,B_280)),u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_279,'#skF_5',B_280)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_279))
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | v2_struct_0(A_279)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_279,B_280)) = B_37
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_279,B_280),B_37)
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_918])).

tff(c_2911,plain,(
    ! [B_485,A_486,B_487] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_485,k5_waybel_0(A_486,B_487)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_485,k5_waybel_0(A_486,B_487)),u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_486,'#skF_5',B_487)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_486))
      | ~ m1_subset_1(B_487,u1_struct_0(A_486))
      | ~ l1_orders_2(A_486)
      | v2_struct_0(A_486)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_486,B_487)) = B_485
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_486,B_487),B_485)
      | ~ m1_subset_1(B_485,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_922])).

tff(c_2915,plain,(
    ! [B_37,A_486,B_487] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_37,k5_waybel_0(A_486,B_487)))
      | ~ r1_orders_2(A_486,'#skF_5',B_487)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_486))
      | ~ m1_subset_1(B_487,u1_struct_0(A_486))
      | ~ l1_orders_2(A_486)
      | v2_struct_0(A_486)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_486,B_487)) = B_37
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_486,B_487),B_37)
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_2911])).

tff(c_2926,plain,(
    ! [B_488,A_489,B_490] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_488,k5_waybel_0(A_489,B_490)))
      | ~ r1_orders_2(A_489,'#skF_5',B_490)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_489))
      | ~ m1_subset_1(B_490,u1_struct_0(A_489))
      | ~ l1_orders_2(A_489)
      | v2_struct_0(A_489)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_489,B_490)) = B_488
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_489,B_490),B_488)
      | ~ m1_subset_1(B_488,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_2915])).

tff(c_32,plain,(
    ! [A_25,B_37,C_43] :
      ( ~ r1_orders_2(A_25,B_37,'#skF_2'(A_25,B_37,C_43))
      | k1_yellow_0(A_25,C_43) = B_37
      | ~ r2_lattice3(A_25,C_43,B_37)
      | ~ m1_subset_1(B_37,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v5_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2930,plain,(
    ! [A_489,B_490] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_orders_2(A_489,'#skF_5',B_490)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_489))
      | ~ m1_subset_1(B_490,u1_struct_0(A_489))
      | ~ l1_orders_2(A_489)
      | v2_struct_0(A_489)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_489,B_490)) = '#skF_5'
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_489,B_490),'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2926,c_32])).

tff(c_2941,plain,(
    ! [A_491,B_492] :
      ( ~ r1_orders_2(A_491,'#skF_5',B_492)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_491))
      | ~ m1_subset_1(B_492,u1_struct_0(A_491))
      | ~ l1_orders_2(A_491)
      | v2_struct_0(A_491)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_491,B_492)) = '#skF_5'
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_491,B_492),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_78,c_72,c_2930])).

tff(c_2945,plain,
    ( ~ r1_orders_2('#skF_4','#skF_5','#skF_5')
    | k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_1004,c_2941])).

tff(c_2948,plain,
    ( k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_226,c_2945])).

tff(c_2949,plain,(
    k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_2948])).

tff(c_38,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k5_waybel_0(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_20,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k1_yellow_0(A_23,B_24),u1_struct_0(A_23))
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_433,plain,(
    ! [A_208,C_209] :
      ( v4_waybel_7(k1_yellow_0(A_208,C_209),A_208)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ v1_waybel_7(C_209,A_208)
      | ~ v12_waybel_0(C_209,A_208)
      | ~ v1_waybel_0(C_209,A_208)
      | v1_xboole_0(C_209)
      | ~ m1_subset_1(k1_yellow_0(A_208,C_209),u1_struct_0(A_208))
      | ~ l1_orders_2(A_208)
      | ~ v2_lattice3(A_208)
      | ~ v1_lattice3(A_208)
      | ~ v5_orders_2(A_208)
      | ~ v4_orders_2(A_208)
      | ~ v3_orders_2(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_867,plain,(
    ! [A_262,B_263] :
      ( v4_waybel_7(k1_yellow_0(A_262,B_263),A_262)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ v1_waybel_7(B_263,A_262)
      | ~ v12_waybel_0(B_263,A_262)
      | ~ v1_waybel_0(B_263,A_262)
      | v1_xboole_0(B_263)
      | ~ v2_lattice3(A_262)
      | ~ v1_lattice3(A_262)
      | ~ v5_orders_2(A_262)
      | ~ v4_orders_2(A_262)
      | ~ v3_orders_2(A_262)
      | ~ l1_orders_2(A_262) ) ),
    inference(resolution,[status(thm)],[c_20,c_433])).

tff(c_873,plain,(
    ! [A_47,B_48] :
      ( v4_waybel_7(k1_yellow_0(A_47,k5_waybel_0(A_47,B_48)),A_47)
      | ~ v1_waybel_7(k5_waybel_0(A_47,B_48),A_47)
      | ~ v12_waybel_0(k5_waybel_0(A_47,B_48),A_47)
      | ~ v1_waybel_0(k5_waybel_0(A_47,B_48),A_47)
      | v1_xboole_0(k5_waybel_0(A_47,B_48))
      | ~ v2_lattice3(A_47)
      | ~ v1_lattice3(A_47)
      | ~ v5_orders_2(A_47)
      | ~ v4_orders_2(A_47)
      | ~ v3_orders_2(A_47)
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_38,c_867])).

tff(c_3001,plain,
    ( v4_waybel_7('#skF_5','#skF_4')
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2949,c_873])).

tff(c_3160,plain,
    ( v4_waybel_7('#skF_5','#skF_4')
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_82,c_80,c_78,c_76,c_74,c_3001])).

tff(c_3161,plain,
    ( ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_97,c_66,c_3160])).

tff(c_3330,plain,(
    ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3161])).

tff(c_3333,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_3330])).

tff(c_3336,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_72,c_70,c_3333])).

tff(c_3338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_3336])).

tff(c_3339,plain,
    ( ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3161])).

tff(c_3341,plain,(
    ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3339])).

tff(c_3344,plain,
    ( ~ v5_waybel_6('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3341])).

tff(c_3348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_3344])).

tff(c_3349,plain,(
    ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3339])).

tff(c_3353,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_3349])).

tff(c_3356,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_72,c_70,c_3353])).

tff(c_3358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_3356])).

tff(c_3359,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_3363,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_3359,c_10])).

tff(c_3367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_3363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.28  
% 6.45/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.28  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 6.45/2.28  
% 6.45/2.28  %Foreground sorts:
% 6.45/2.28  
% 6.45/2.28  
% 6.45/2.28  %Background operators:
% 6.45/2.28  
% 6.45/2.28  
% 6.45/2.28  %Foreground operators:
% 6.45/2.28  tff(v1_waybel_7, type, v1_waybel_7: ($i * $i) > $o).
% 6.45/2.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.45/2.28  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 6.45/2.28  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 6.45/2.28  tff(v5_waybel_6, type, v5_waybel_6: ($i * $i) > $o).
% 6.45/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.45/2.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.45/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.45/2.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.45/2.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.45/2.28  tff(v12_waybel_0, type, v12_waybel_0: ($i * $i) > $o).
% 6.45/2.28  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 6.45/2.28  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 6.45/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.45/2.28  tff(v4_waybel_7, type, v4_waybel_7: ($i * $i) > $o).
% 6.45/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.45/2.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.45/2.28  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 6.45/2.28  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 6.45/2.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.45/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.45/2.28  tff(v1_waybel_0, type, v1_waybel_0: ($i * $i) > $o).
% 6.45/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.45/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.28  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 6.45/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.45/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.45/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.28  
% 6.66/2.30  tff(f_237, negated_conjecture, ~(![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v4_waybel_7(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_7)).
% 6.66/2.30  tff(f_59, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 6.66/2.30  tff(f_66, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 6.66/2.30  tff(f_138, axiom, (![A, B]: ((((~v2_struct_0(A) & v4_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => v12_waybel_0(k5_waybel_0(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_waybel_0)).
% 6.66/2.30  tff(f_217, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v1_waybel_7(k5_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_waybel_7)).
% 6.66/2.30  tff(f_152, axiom, (![A, B]: ((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => (~v1_xboole_0(k5_waybel_0(A, B)) & v1_waybel_0(k5_waybel_0(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_waybel_0)).
% 6.66/2.30  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 6.66/2.30  tff(f_80, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 6.66/2.30  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k5_waybel_0(A, B)) <=> r1_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_waybel_0)).
% 6.66/2.30  tff(f_118, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 6.66/2.30  tff(f_127, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k5_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 6.66/2.30  tff(f_84, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 6.66/2.30  tff(f_198, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v4_waybel_7(B, A) <=> (?[C]: (((((~v1_xboole_0(C) & v1_waybel_0(C, A)) & v12_waybel_0(C, A)) & v1_waybel_7(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) & (B = k1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_waybel_7)).
% 6.66/2.30  tff(c_72, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_76, plain, (v1_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_82, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_70, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_118, plain, (![A_102, B_103, C_104]: (r3_orders_2(A_102, B_103, B_103) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.66/2.30  tff(c_124, plain, (![B_103]: (r3_orders_2('#skF_4', B_103, B_103) | ~m1_subset_1(B_103, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_118])).
% 6.66/2.30  tff(c_129, plain, (![B_103]: (r3_orders_2('#skF_4', B_103, B_103) | ~m1_subset_1(B_103, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_72, c_124])).
% 6.66/2.30  tff(c_130, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_129])).
% 6.66/2.30  tff(c_10, plain, (![A_10]: (~v2_struct_0(A_10) | ~v1_lattice3(A_10) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.66/2.30  tff(c_137, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_130, c_10])).
% 6.66/2.30  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_137])).
% 6.66/2.30  tff(c_143, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_129])).
% 6.66/2.30  tff(c_80, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_40, plain, (![A_49, B_50]: (v12_waybel_0(k5_waybel_0(A_49, B_50), A_49) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_orders_2(A_49) | ~v4_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.66/2.30  tff(c_78, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_74, plain, (v2_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_68, plain, (v5_waybel_6('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_64, plain, (![A_70, B_72]: (v1_waybel_7(k5_waybel_0(A_70, B_72), A_70) | ~v5_waybel_6(B_72, A_70) | ~m1_subset_1(B_72, u1_struct_0(A_70)) | ~l1_orders_2(A_70) | ~v2_lattice3(A_70) | ~v1_lattice3(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_217])).
% 6.66/2.30  tff(c_42, plain, (![A_51, B_52]: (v1_waybel_0(k5_waybel_0(A_51, B_52), A_51) | ~m1_subset_1(B_52, u1_struct_0(A_51)) | ~l1_orders_2(A_51) | ~v3_orders_2(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.66/2.30  tff(c_86, plain, (![A_80, B_81]: (~v1_xboole_0(k5_waybel_0(A_80, B_81)) | ~m1_subset_1(B_81, u1_struct_0(A_80)) | ~l1_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.66/2.30  tff(c_92, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_86])).
% 6.66/2.30  tff(c_96, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_72, c_92])).
% 6.66/2.30  tff(c_97, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_96])).
% 6.66/2.30  tff(c_66, plain, (~v4_waybel_7('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 6.66/2.30  tff(c_144, plain, (![B_107]: (r3_orders_2('#skF_4', B_107, B_107) | ~m1_subset_1(B_107, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_129])).
% 6.66/2.30  tff(c_159, plain, (r3_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_144])).
% 6.66/2.30  tff(c_205, plain, (![A_135, B_136, C_137]: (r1_orders_2(A_135, B_136, C_137) | ~r3_orders_2(A_135, B_136, C_137) | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.66/2.30  tff(c_213, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_159, c_205])).
% 6.66/2.30  tff(c_225, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_72, c_70, c_213])).
% 6.66/2.30  tff(c_226, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_143, c_225])).
% 6.66/2.30  tff(c_18, plain, (![A_11, B_18, C_19]: (m1_subset_1('#skF_1'(A_11, B_18, C_19), u1_struct_0(A_11)) | r2_lattice3(A_11, B_18, C_19) | ~m1_subset_1(C_19, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.66/2.30  tff(c_16, plain, (![A_11, B_18, C_19]: (r2_hidden('#skF_1'(A_11, B_18, C_19), B_18) | r2_lattice3(A_11, B_18, C_19) | ~m1_subset_1(C_19, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.66/2.30  tff(c_186, plain, (![A_122, C_123, B_124]: (r1_orders_2(A_122, C_123, B_124) | ~r2_hidden(C_123, k5_waybel_0(A_122, B_124)) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1(B_124, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.66/2.30  tff(c_990, plain, (![A_313, A_314, B_315, C_316]: (r1_orders_2(A_313, '#skF_1'(A_314, k5_waybel_0(A_313, B_315), C_316), B_315) | ~m1_subset_1('#skF_1'(A_314, k5_waybel_0(A_313, B_315), C_316), u1_struct_0(A_313)) | ~m1_subset_1(B_315, u1_struct_0(A_313)) | ~l1_orders_2(A_313) | v2_struct_0(A_313) | r2_lattice3(A_314, k5_waybel_0(A_313, B_315), C_316) | ~m1_subset_1(C_316, u1_struct_0(A_314)) | ~l1_orders_2(A_314))), inference(resolution, [status(thm)], [c_16, c_186])).
% 6.66/2.30  tff(c_999, plain, (![A_320, B_321, C_322]: (r1_orders_2(A_320, '#skF_1'(A_320, k5_waybel_0(A_320, B_321), C_322), B_321) | ~m1_subset_1(B_321, u1_struct_0(A_320)) | v2_struct_0(A_320) | r2_lattice3(A_320, k5_waybel_0(A_320, B_321), C_322) | ~m1_subset_1(C_322, u1_struct_0(A_320)) | ~l1_orders_2(A_320))), inference(resolution, [status(thm)], [c_18, c_990])).
% 6.66/2.30  tff(c_14, plain, (![A_11, B_18, C_19]: (~r1_orders_2(A_11, '#skF_1'(A_11, B_18, C_19), C_19) | r2_lattice3(A_11, B_18, C_19) | ~m1_subset_1(C_19, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.66/2.30  tff(c_1004, plain, (![A_320, B_321]: (v2_struct_0(A_320) | r2_lattice3(A_320, k5_waybel_0(A_320, B_321), B_321) | ~m1_subset_1(B_321, u1_struct_0(A_320)) | ~l1_orders_2(A_320))), inference(resolution, [status(thm)], [c_999, c_14])).
% 6.66/2.30  tff(c_36, plain, (![A_25, B_37, C_43]: (m1_subset_1('#skF_2'(A_25, B_37, C_43), u1_struct_0(A_25)) | k1_yellow_0(A_25, C_43)=B_37 | ~r2_lattice3(A_25, C_43, B_37) | ~m1_subset_1(B_37, u1_struct_0(A_25)) | ~l1_orders_2(A_25) | ~v5_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.66/2.30  tff(c_34, plain, (![A_25, C_43, B_37]: (r2_lattice3(A_25, C_43, '#skF_2'(A_25, B_37, C_43)) | k1_yellow_0(A_25, C_43)=B_37 | ~r2_lattice3(A_25, C_43, B_37) | ~m1_subset_1(B_37, u1_struct_0(A_25)) | ~l1_orders_2(A_25) | ~v5_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.66/2.30  tff(c_46, plain, (![C_59, A_53, B_57]: (r2_hidden(C_59, k5_waybel_0(A_53, B_57)) | ~r1_orders_2(A_53, C_59, B_57) | ~m1_subset_1(C_59, u1_struct_0(A_53)) | ~m1_subset_1(B_57, u1_struct_0(A_53)) | ~l1_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.66/2.30  tff(c_196, plain, (![A_125, D_126, C_127, B_128]: (r1_orders_2(A_125, D_126, C_127) | ~r2_hidden(D_126, B_128) | ~m1_subset_1(D_126, u1_struct_0(A_125)) | ~r2_lattice3(A_125, B_128, C_127) | ~m1_subset_1(C_127, u1_struct_0(A_125)) | ~l1_orders_2(A_125))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.66/2.30  tff(c_897, plain, (![B_274, C_277, C_275, A_276, A_273]: (r1_orders_2(A_276, C_277, C_275) | ~m1_subset_1(C_277, u1_struct_0(A_276)) | ~r2_lattice3(A_276, k5_waybel_0(A_273, B_274), C_275) | ~m1_subset_1(C_275, u1_struct_0(A_276)) | ~l1_orders_2(A_276) | ~r1_orders_2(A_273, C_277, B_274) | ~m1_subset_1(C_277, u1_struct_0(A_273)) | ~m1_subset_1(B_274, u1_struct_0(A_273)) | ~l1_orders_2(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_46, c_196])).
% 6.66/2.30  tff(c_909, plain, (![C_275, A_273, B_274]: (r1_orders_2('#skF_4', '#skF_5', C_275) | ~r2_lattice3('#skF_4', k5_waybel_0(A_273, B_274), C_275) | ~m1_subset_1(C_275, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r1_orders_2(A_273, '#skF_5', B_274) | ~m1_subset_1('#skF_5', u1_struct_0(A_273)) | ~m1_subset_1(B_274, u1_struct_0(A_273)) | ~l1_orders_2(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_70, c_897])).
% 6.66/2.30  tff(c_918, plain, (![C_278, A_279, B_280]: (r1_orders_2('#skF_4', '#skF_5', C_278) | ~r2_lattice3('#skF_4', k5_waybel_0(A_279, B_280), C_278) | ~m1_subset_1(C_278, u1_struct_0('#skF_4')) | ~r1_orders_2(A_279, '#skF_5', B_280) | ~m1_subset_1('#skF_5', u1_struct_0(A_279)) | ~m1_subset_1(B_280, u1_struct_0(A_279)) | ~l1_orders_2(A_279) | v2_struct_0(A_279))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_909])).
% 6.66/2.30  tff(c_922, plain, (![B_37, A_279, B_280]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_37, k5_waybel_0(A_279, B_280))) | ~m1_subset_1('#skF_2'('#skF_4', B_37, k5_waybel_0(A_279, B_280)), u1_struct_0('#skF_4')) | ~r1_orders_2(A_279, '#skF_5', B_280) | ~m1_subset_1('#skF_5', u1_struct_0(A_279)) | ~m1_subset_1(B_280, u1_struct_0(A_279)) | ~l1_orders_2(A_279) | v2_struct_0(A_279) | k1_yellow_0('#skF_4', k5_waybel_0(A_279, B_280))=B_37 | ~r2_lattice3('#skF_4', k5_waybel_0(A_279, B_280), B_37) | ~m1_subset_1(B_37, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_918])).
% 6.66/2.30  tff(c_2911, plain, (![B_485, A_486, B_487]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_485, k5_waybel_0(A_486, B_487))) | ~m1_subset_1('#skF_2'('#skF_4', B_485, k5_waybel_0(A_486, B_487)), u1_struct_0('#skF_4')) | ~r1_orders_2(A_486, '#skF_5', B_487) | ~m1_subset_1('#skF_5', u1_struct_0(A_486)) | ~m1_subset_1(B_487, u1_struct_0(A_486)) | ~l1_orders_2(A_486) | v2_struct_0(A_486) | k1_yellow_0('#skF_4', k5_waybel_0(A_486, B_487))=B_485 | ~r2_lattice3('#skF_4', k5_waybel_0(A_486, B_487), B_485) | ~m1_subset_1(B_485, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_922])).
% 6.66/2.30  tff(c_2915, plain, (![B_37, A_486, B_487]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_37, k5_waybel_0(A_486, B_487))) | ~r1_orders_2(A_486, '#skF_5', B_487) | ~m1_subset_1('#skF_5', u1_struct_0(A_486)) | ~m1_subset_1(B_487, u1_struct_0(A_486)) | ~l1_orders_2(A_486) | v2_struct_0(A_486) | k1_yellow_0('#skF_4', k5_waybel_0(A_486, B_487))=B_37 | ~r2_lattice3('#skF_4', k5_waybel_0(A_486, B_487), B_37) | ~m1_subset_1(B_37, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_2911])).
% 6.66/2.30  tff(c_2926, plain, (![B_488, A_489, B_490]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_488, k5_waybel_0(A_489, B_490))) | ~r1_orders_2(A_489, '#skF_5', B_490) | ~m1_subset_1('#skF_5', u1_struct_0(A_489)) | ~m1_subset_1(B_490, u1_struct_0(A_489)) | ~l1_orders_2(A_489) | v2_struct_0(A_489) | k1_yellow_0('#skF_4', k5_waybel_0(A_489, B_490))=B_488 | ~r2_lattice3('#skF_4', k5_waybel_0(A_489, B_490), B_488) | ~m1_subset_1(B_488, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_2915])).
% 6.66/2.30  tff(c_32, plain, (![A_25, B_37, C_43]: (~r1_orders_2(A_25, B_37, '#skF_2'(A_25, B_37, C_43)) | k1_yellow_0(A_25, C_43)=B_37 | ~r2_lattice3(A_25, C_43, B_37) | ~m1_subset_1(B_37, u1_struct_0(A_25)) | ~l1_orders_2(A_25) | ~v5_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.66/2.30  tff(c_2930, plain, (![A_489, B_490]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r1_orders_2(A_489, '#skF_5', B_490) | ~m1_subset_1('#skF_5', u1_struct_0(A_489)) | ~m1_subset_1(B_490, u1_struct_0(A_489)) | ~l1_orders_2(A_489) | v2_struct_0(A_489) | k1_yellow_0('#skF_4', k5_waybel_0(A_489, B_490))='#skF_5' | ~r2_lattice3('#skF_4', k5_waybel_0(A_489, B_490), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2926, c_32])).
% 6.66/2.30  tff(c_2941, plain, (![A_491, B_492]: (~r1_orders_2(A_491, '#skF_5', B_492) | ~m1_subset_1('#skF_5', u1_struct_0(A_491)) | ~m1_subset_1(B_492, u1_struct_0(A_491)) | ~l1_orders_2(A_491) | v2_struct_0(A_491) | k1_yellow_0('#skF_4', k5_waybel_0(A_491, B_492))='#skF_5' | ~r2_lattice3('#skF_4', k5_waybel_0(A_491, B_492), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_78, c_72, c_2930])).
% 6.66/2.30  tff(c_2945, plain, (~r1_orders_2('#skF_4', '#skF_5', '#skF_5') | k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5' | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_1004, c_2941])).
% 6.66/2.30  tff(c_2948, plain, (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_226, c_2945])).
% 6.66/2.30  tff(c_2949, plain, (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_143, c_2948])).
% 6.66/2.30  tff(c_38, plain, (![A_47, B_48]: (m1_subset_1(k5_waybel_0(A_47, B_48), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_orders_2(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.66/2.30  tff(c_20, plain, (![A_23, B_24]: (m1_subset_1(k1_yellow_0(A_23, B_24), u1_struct_0(A_23)) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.66/2.30  tff(c_433, plain, (![A_208, C_209]: (v4_waybel_7(k1_yellow_0(A_208, C_209), A_208) | ~m1_subset_1(C_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~v1_waybel_7(C_209, A_208) | ~v12_waybel_0(C_209, A_208) | ~v1_waybel_0(C_209, A_208) | v1_xboole_0(C_209) | ~m1_subset_1(k1_yellow_0(A_208, C_209), u1_struct_0(A_208)) | ~l1_orders_2(A_208) | ~v2_lattice3(A_208) | ~v1_lattice3(A_208) | ~v5_orders_2(A_208) | ~v4_orders_2(A_208) | ~v3_orders_2(A_208))), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.66/2.30  tff(c_867, plain, (![A_262, B_263]: (v4_waybel_7(k1_yellow_0(A_262, B_263), A_262) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~v1_waybel_7(B_263, A_262) | ~v12_waybel_0(B_263, A_262) | ~v1_waybel_0(B_263, A_262) | v1_xboole_0(B_263) | ~v2_lattice3(A_262) | ~v1_lattice3(A_262) | ~v5_orders_2(A_262) | ~v4_orders_2(A_262) | ~v3_orders_2(A_262) | ~l1_orders_2(A_262))), inference(resolution, [status(thm)], [c_20, c_433])).
% 6.66/2.30  tff(c_873, plain, (![A_47, B_48]: (v4_waybel_7(k1_yellow_0(A_47, k5_waybel_0(A_47, B_48)), A_47) | ~v1_waybel_7(k5_waybel_0(A_47, B_48), A_47) | ~v12_waybel_0(k5_waybel_0(A_47, B_48), A_47) | ~v1_waybel_0(k5_waybel_0(A_47, B_48), A_47) | v1_xboole_0(k5_waybel_0(A_47, B_48)) | ~v2_lattice3(A_47) | ~v1_lattice3(A_47) | ~v5_orders_2(A_47) | ~v4_orders_2(A_47) | ~v3_orders_2(A_47) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_orders_2(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_38, c_867])).
% 6.66/2.30  tff(c_3001, plain, (v4_waybel_7('#skF_5', '#skF_4') | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2949, c_873])).
% 6.66/2.30  tff(c_3160, plain, (v4_waybel_7('#skF_5', '#skF_4') | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_82, c_80, c_78, c_76, c_74, c_3001])).
% 6.66/2.30  tff(c_3161, plain, (~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_143, c_97, c_66, c_3160])).
% 6.66/2.30  tff(c_3330, plain, (~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3161])).
% 6.66/2.30  tff(c_3333, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_3330])).
% 6.66/2.30  tff(c_3336, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_72, c_70, c_3333])).
% 6.66/2.30  tff(c_3338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_3336])).
% 6.66/2.30  tff(c_3339, plain, (~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_3161])).
% 6.66/2.30  tff(c_3341, plain, (~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3339])).
% 6.66/2.30  tff(c_3344, plain, (~v5_waybel_6('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_64, c_3341])).
% 6.66/2.30  tff(c_3348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_3344])).
% 6.66/2.30  tff(c_3349, plain, (~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_3339])).
% 6.66/2.30  tff(c_3353, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_3349])).
% 6.66/2.30  tff(c_3356, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_72, c_70, c_3353])).
% 6.66/2.30  tff(c_3358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_3356])).
% 6.66/2.30  tff(c_3359, plain, (v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_96])).
% 6.66/2.30  tff(c_3363, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_3359, c_10])).
% 6.66/2.30  tff(c_3367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_3363])).
% 6.66/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.30  
% 6.66/2.30  Inference rules
% 6.66/2.30  ----------------------
% 6.66/2.30  #Ref     : 0
% 6.66/2.30  #Sup     : 619
% 6.66/2.30  #Fact    : 0
% 6.66/2.30  #Define  : 0
% 6.66/2.30  #Split   : 4
% 6.66/2.30  #Chain   : 0
% 6.66/2.30  #Close   : 0
% 6.66/2.30  
% 6.66/2.30  Ordering : KBO
% 6.66/2.30  
% 6.66/2.30  Simplification rules
% 6.66/2.30  ----------------------
% 6.66/2.30  #Subsume      : 231
% 6.66/2.30  #Demod        : 2062
% 6.66/2.30  #Tautology    : 78
% 6.66/2.30  #SimpNegUnit  : 65
% 6.66/2.30  #BackRed      : 0
% 6.66/2.30  
% 6.66/2.30  #Partial instantiations: 0
% 6.66/2.30  #Strategies tried      : 1
% 6.66/2.30  
% 6.66/2.30  Timing (in seconds)
% 6.66/2.30  ----------------------
% 6.66/2.31  Preprocessing        : 0.35
% 6.66/2.31  Parsing              : 0.19
% 6.66/2.31  CNF conversion       : 0.03
% 6.66/2.31  Main loop            : 1.13
% 6.66/2.31  Inferencing          : 0.48
% 6.66/2.31  Reduction            : 0.35
% 6.66/2.31  Demodulation         : 0.25
% 6.66/2.31  BG Simplification    : 0.05
% 6.66/2.31  Subsumption          : 0.21
% 6.66/2.31  Abstraction          : 0.05
% 6.66/2.31  MUC search           : 0.00
% 6.66/2.31  Cooper               : 0.00
% 6.66/2.31  Total                : 1.53
% 6.66/2.31  Index Insertion      : 0.00
% 6.66/2.31  Index Deletion       : 0.00
% 6.66/2.31  Index Matching       : 0.00
% 6.66/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
