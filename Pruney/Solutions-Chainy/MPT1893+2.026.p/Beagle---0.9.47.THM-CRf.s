%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:29 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 146 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 518 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_69,plain,(
    ! [A_30,B_31] :
      ( k2_pre_topc(A_30,B_31) = B_31
      | ~ v4_pre_topc(B_31,A_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_83,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_78])).

tff(c_84,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_47,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_163,plain,(
    ! [B_47,A_48] :
      ( v4_pre_topc(B_47,A_48)
      | ~ v3_pre_topc(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v3_tdlat_3(A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_172,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_177,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_47,c_172])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_177])).

tff(c_180,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_186,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = u1_struct_0(A_49)
      | ~ v1_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_195,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_186])).

tff(c_200,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_180,c_195])).

tff(c_201,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_34,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_297,plain,(
    ! [B_69,A_70] :
      ( v1_tops_1(B_69,A_70)
      | ~ v3_tex_2(B_69,A_70)
      | ~ v3_pre_topc(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_306,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_297])).

tff(c_311,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_47,c_34,c_306])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_201,c_311])).

tff(c_314,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_32,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_317,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_32])).

tff(c_316,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_38])).

tff(c_12,plain,(
    ! [B_8] :
      ( ~ v1_subset_1(B_8,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_347,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_316,c_12])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_347])).

tff(c_356,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_355,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_466,plain,(
    ! [B_94,A_95] :
      ( v3_pre_topc(B_94,A_95)
      | ~ v4_pre_topc(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v3_tdlat_3(A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_475,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_466])).

tff(c_480,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_355,c_475])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.45  
% 2.41/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.45  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.41/1.45  
% 2.41/1.45  %Foreground sorts:
% 2.41/1.45  
% 2.41/1.45  
% 2.41/1.45  %Background operators:
% 2.41/1.45  
% 2.41/1.45  
% 2.41/1.45  %Foreground operators:
% 2.41/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.41/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.41/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.41/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.45  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.41/1.45  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.41/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.45  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.41/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.41/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.41/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.45  
% 2.52/1.47  tff(f_120, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 2.52/1.47  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.52/1.47  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 2.52/1.47  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 2.52/1.47  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 2.52/1.47  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.52/1.47  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.52/1.47  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_69, plain, (![A_30, B_31]: (k2_pre_topc(A_30, B_31)=B_31 | ~v4_pre_topc(B_31, A_30) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.47  tff(c_78, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_69])).
% 2.52/1.47  tff(c_83, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_78])).
% 2.52/1.47  tff(c_84, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_83])).
% 2.52/1.47  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_42, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_36, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_47, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.52/1.47  tff(c_163, plain, (![B_47, A_48]: (v4_pre_topc(B_47, A_48) | ~v3_pre_topc(B_47, A_48) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_48))) | ~v3_tdlat_3(A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.52/1.47  tff(c_172, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_163])).
% 2.52/1.47  tff(c_177, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_47, c_172])).
% 2.52/1.47  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_177])).
% 2.52/1.47  tff(c_180, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_83])).
% 2.52/1.47  tff(c_186, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=u1_struct_0(A_49) | ~v1_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.52/1.47  tff(c_195, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_186])).
% 2.52/1.47  tff(c_200, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_180, c_195])).
% 2.52/1.47  tff(c_201, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_200])).
% 2.52/1.47  tff(c_34, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_297, plain, (![B_69, A_70]: (v1_tops_1(B_69, A_70) | ~v3_tex_2(B_69, A_70) | ~v3_pre_topc(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.52/1.47  tff(c_306, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_297])).
% 2.52/1.47  tff(c_311, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_47, c_34, c_306])).
% 2.52/1.47  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_201, c_311])).
% 2.52/1.47  tff(c_314, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_200])).
% 2.52/1.47  tff(c_32, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.52/1.47  tff(c_317, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_32])).
% 2.52/1.47  tff(c_316, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_38])).
% 2.52/1.47  tff(c_12, plain, (![B_8]: (~v1_subset_1(B_8, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.52/1.47  tff(c_347, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_316, c_12])).
% 2.52/1.47  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_347])).
% 2.52/1.47  tff(c_356, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.52/1.47  tff(c_355, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.52/1.47  tff(c_466, plain, (![B_94, A_95]: (v3_pre_topc(B_94, A_95) | ~v4_pre_topc(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~v3_tdlat_3(A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.52/1.47  tff(c_475, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_466])).
% 2.52/1.47  tff(c_480, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_355, c_475])).
% 2.52/1.47  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_480])).
% 2.52/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.47  
% 2.52/1.47  Inference rules
% 2.52/1.47  ----------------------
% 2.52/1.47  #Ref     : 0
% 2.52/1.47  #Sup     : 81
% 2.52/1.47  #Fact    : 0
% 2.52/1.47  #Define  : 0
% 2.52/1.47  #Split   : 5
% 2.52/1.47  #Chain   : 0
% 2.52/1.47  #Close   : 0
% 2.52/1.47  
% 2.52/1.47  Ordering : KBO
% 2.52/1.47  
% 2.52/1.47  Simplification rules
% 2.52/1.47  ----------------------
% 2.52/1.47  #Subsume      : 16
% 2.52/1.47  #Demod        : 64
% 2.52/1.47  #Tautology    : 27
% 2.52/1.47  #SimpNegUnit  : 7
% 2.52/1.47  #BackRed      : 2
% 2.52/1.47  
% 2.52/1.47  #Partial instantiations: 0
% 2.52/1.47  #Strategies tried      : 1
% 2.52/1.47  
% 2.52/1.47  Timing (in seconds)
% 2.52/1.47  ----------------------
% 2.52/1.47  Preprocessing        : 0.29
% 2.52/1.47  Parsing              : 0.15
% 2.52/1.47  CNF conversion       : 0.02
% 2.52/1.47  Main loop            : 0.27
% 2.52/1.47  Inferencing          : 0.11
% 2.52/1.47  Reduction            : 0.07
% 2.52/1.47  Demodulation         : 0.05
% 2.52/1.47  BG Simplification    : 0.02
% 2.52/1.47  Subsumption          : 0.04
% 2.52/1.47  Abstraction          : 0.02
% 2.52/1.47  MUC search           : 0.00
% 2.52/1.47  Cooper               : 0.00
% 2.52/1.47  Total                : 0.59
% 2.52/1.47  Index Insertion      : 0.00
% 2.52/1.47  Index Deletion       : 0.00
% 2.52/1.47  Index Matching       : 0.00
% 2.52/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
