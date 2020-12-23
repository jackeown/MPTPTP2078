%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:27 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 152 expanded)
%              Number of leaves         :   38 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 468 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_pre_topc > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_61,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_14,plain,(
    ! [A_7] : l1_orders_2(k2_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_121,plain,(
    ! [A_40,B_41] :
      ( k2_pre_topc(A_40,B_41) = B_41
      | ~ v4_pre_topc(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_130,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_121])).

tff(c_138,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_130])).

tff(c_139,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_78,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_242,plain,(
    ! [B_51,A_52] :
      ( v4_pre_topc(B_51,A_52)
      | ~ v3_pre_topc(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ v3_tdlat_3(A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_259,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_242])).

tff(c_269,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_78,c_259])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_269])).

tff(c_272,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_278,plain,(
    ! [A_53,B_54] :
      ( k2_pre_topc(A_53,B_54) = u1_struct_0(A_53)
      | ~ v1_tops_1(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_287,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_278])).

tff(c_295,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_272,c_287])).

tff(c_297,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_44,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_517,plain,(
    ! [B_81,A_82] :
      ( v1_tops_1(B_81,A_82)
      | ~ v3_tex_2(B_81,A_82)
      | ~ v3_pre_topc(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_534,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_517])).

tff(c_544,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_78,c_44,c_534])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_297,c_544])).

tff(c_547,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_42,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_569,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_42])).

tff(c_16,plain,(
    ! [A_8] : u1_struct_0(k2_yellow_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_91,plain,(
    ! [A_7] : u1_struct_0(k2_yellow_1(A_7)) = k2_struct_0(k2_yellow_1(A_7)) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_94,plain,(
    ! [A_32] : k2_struct_0(k2_yellow_1(A_32)) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_subset_1(k2_struct_0(A_2),u1_struct_0(A_2))
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_100,plain,(
    ! [A_32] :
      ( ~ v1_subset_1(A_32,u1_struct_0(k2_yellow_1(A_32)))
      | ~ l1_struct_0(k2_yellow_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4])).

tff(c_105,plain,(
    ! [A_32] :
      ( ~ v1_subset_1(A_32,A_32)
      | ~ l1_struct_0(k2_yellow_1(A_32)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_100])).

tff(c_604,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_569,c_105])).

tff(c_607,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_604])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_607])).

tff(c_613,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_612,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_778,plain,(
    ! [B_106,A_107] :
      ( v3_pre_topc(B_106,A_107)
      | ~ v4_pre_topc(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v3_tdlat_3(A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_795,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_778])).

tff(c_805,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_612,c_795])).

tff(c_807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:41:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  
% 3.02/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_pre_topc > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.02/1.47  
% 3.02/1.47  %Foreground sorts:
% 3.02/1.47  
% 3.02/1.47  
% 3.02/1.47  %Background operators:
% 3.02/1.47  
% 3.02/1.47  
% 3.02/1.47  %Foreground operators:
% 3.02/1.47  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.02/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.02/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.02/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.02/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.02/1.47  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.02/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.47  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.02/1.47  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.02/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.02/1.47  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.02/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.02/1.47  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.47  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.02/1.47  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.02/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.02/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.02/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.47  
% 3.23/1.49  tff(f_57, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.23/1.49  tff(f_53, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.23/1.49  tff(f_134, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 3.23/1.49  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.23/1.49  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.23/1.49  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 3.23/1.49  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 3.23/1.49  tff(f_61, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.23/1.49  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.23/1.49  tff(f_34, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 3.23/1.49  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.23/1.49  tff(c_14, plain, (![A_7]: (l1_orders_2(k2_yellow_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.49  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.49  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_121, plain, (![A_40, B_41]: (k2_pre_topc(A_40, B_41)=B_41 | ~v4_pre_topc(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.49  tff(c_130, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_121])).
% 3.23/1.49  tff(c_138, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_130])).
% 3.23/1.49  tff(c_139, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_138])).
% 3.23/1.49  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_52, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_46, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_78, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.23/1.49  tff(c_242, plain, (![B_51, A_52]: (v4_pre_topc(B_51, A_52) | ~v3_pre_topc(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~v3_tdlat_3(A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.49  tff(c_259, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_242])).
% 3.23/1.49  tff(c_269, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_78, c_259])).
% 3.23/1.49  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_269])).
% 3.23/1.49  tff(c_272, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_138])).
% 3.23/1.49  tff(c_278, plain, (![A_53, B_54]: (k2_pre_topc(A_53, B_54)=u1_struct_0(A_53) | ~v1_tops_1(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.23/1.49  tff(c_287, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_278])).
% 3.23/1.49  tff(c_295, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_272, c_287])).
% 3.23/1.49  tff(c_297, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_295])).
% 3.23/1.49  tff(c_44, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_517, plain, (![B_81, A_82]: (v1_tops_1(B_81, A_82) | ~v3_tex_2(B_81, A_82) | ~v3_pre_topc(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.49  tff(c_534, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_517])).
% 3.23/1.49  tff(c_544, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_78, c_44, c_534])).
% 3.23/1.49  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_297, c_544])).
% 3.23/1.49  tff(c_547, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_295])).
% 3.23/1.49  tff(c_42, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.23/1.49  tff(c_569, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_42])).
% 3.23/1.49  tff(c_16, plain, (![A_8]: (u1_struct_0(k2_yellow_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.49  tff(c_79, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.49  tff(c_88, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_orders_2(A_31))), inference(resolution, [status(thm)], [c_10, c_79])).
% 3.23/1.49  tff(c_91, plain, (![A_7]: (u1_struct_0(k2_yellow_1(A_7))=k2_struct_0(k2_yellow_1(A_7)))), inference(resolution, [status(thm)], [c_14, c_88])).
% 3.23/1.49  tff(c_94, plain, (![A_32]: (k2_struct_0(k2_yellow_1(A_32))=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_91])).
% 3.23/1.49  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_struct_0(A_2), u1_struct_0(A_2)) | ~l1_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.49  tff(c_100, plain, (![A_32]: (~v1_subset_1(A_32, u1_struct_0(k2_yellow_1(A_32))) | ~l1_struct_0(k2_yellow_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_4])).
% 3.23/1.49  tff(c_105, plain, (![A_32]: (~v1_subset_1(A_32, A_32) | ~l1_struct_0(k2_yellow_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_100])).
% 3.23/1.49  tff(c_604, plain, (~l1_struct_0(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_569, c_105])).
% 3.23/1.49  tff(c_607, plain, (~l1_orders_2(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_604])).
% 3.23/1.49  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_607])).
% 3.23/1.49  tff(c_613, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.23/1.49  tff(c_612, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.23/1.49  tff(c_778, plain, (![B_106, A_107]: (v3_pre_topc(B_106, A_107) | ~v4_pre_topc(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~v3_tdlat_3(A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.49  tff(c_795, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_778])).
% 3.23/1.49  tff(c_805, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_612, c_795])).
% 3.23/1.49  tff(c_807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_613, c_805])).
% 3.23/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  Inference rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Ref     : 0
% 3.23/1.49  #Sup     : 151
% 3.23/1.49  #Fact    : 0
% 3.23/1.49  #Define  : 0
% 3.23/1.49  #Split   : 5
% 3.23/1.49  #Chain   : 0
% 3.23/1.49  #Close   : 0
% 3.23/1.49  
% 3.23/1.49  Ordering : KBO
% 3.23/1.49  
% 3.23/1.49  Simplification rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Subsume      : 15
% 3.23/1.49  #Demod        : 78
% 3.23/1.49  #Tautology    : 35
% 3.23/1.49  #SimpNegUnit  : 7
% 3.23/1.49  #BackRed      : 2
% 3.23/1.49  
% 3.23/1.49  #Partial instantiations: 0
% 3.23/1.49  #Strategies tried      : 1
% 3.23/1.49  
% 3.23/1.49  Timing (in seconds)
% 3.23/1.49  ----------------------
% 3.23/1.49  Preprocessing        : 0.32
% 3.23/1.49  Parsing              : 0.17
% 3.23/1.49  CNF conversion       : 0.02
% 3.23/1.49  Main loop            : 0.37
% 3.23/1.49  Inferencing          : 0.15
% 3.23/1.49  Reduction            : 0.11
% 3.23/1.49  Demodulation         : 0.08
% 3.23/1.49  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.05
% 3.23/1.49  Abstraction          : 0.02
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.72
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
