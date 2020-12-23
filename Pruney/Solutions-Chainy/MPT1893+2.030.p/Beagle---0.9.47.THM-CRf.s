%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:29 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 132 expanded)
%              Number of leaves         :   30 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 451 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_100,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,(
    ! [A_29,B_30] :
      ( k2_pre_topc(A_29,B_30) = B_30
      | ~ v4_pre_topc(B_30,A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_70,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65])).

tff(c_71,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_122,plain,(
    ! [B_39,A_40] :
      ( v4_pre_topc(B_39,A_40)
      | ~ v3_pre_topc(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ v3_tdlat_3(A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_131,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_122])).

tff(c_136,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_48,c_131])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_136])).

tff(c_139,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_145,plain,(
    ! [A_41,B_42] :
      ( k2_pre_topc(A_41,B_42) = k2_struct_0(A_41)
      | ~ v1_tops_1(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_154,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_159,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_139,c_154])).

tff(c_160,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_34,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_254,plain,(
    ! [B_59,A_60] :
      ( v1_tops_1(B_59,A_60)
      | ~ v3_tex_2(B_59,A_60)
      | ~ v3_pre_topc(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_263,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_254])).

tff(c_268,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_48,c_34,c_263])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_160,c_268])).

tff(c_271,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_subset_1(k2_struct_0(A_2),u1_struct_0(A_2))
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_276,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_4])).

tff(c_280,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_276])).

tff(c_284,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_280])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_284])).

tff(c_290,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_289,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_365,plain,(
    ! [B_77,A_78] :
      ( v3_pre_topc(B_77,A_78)
      | ~ v4_pre_topc(B_77,A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v3_tdlat_3(A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_374,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_365])).

tff(c_379,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_289,c_374])).

tff(c_381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.81  
% 2.97/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.82  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.97/1.82  
% 2.97/1.82  %Foreground sorts:
% 2.97/1.82  
% 2.97/1.82  
% 2.97/1.82  %Background operators:
% 2.97/1.82  
% 2.97/1.82  
% 2.97/1.82  %Foreground operators:
% 2.97/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.97/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.97/1.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.97/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.82  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.97/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.97/1.82  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.97/1.82  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.97/1.82  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.97/1.82  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.97/1.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.97/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.82  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.97/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.97/1.82  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.97/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.82  
% 3.13/1.84  tff(f_122, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 3.13/1.84  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.13/1.84  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.13/1.84  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.13/1.84  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.13/1.84  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.13/1.84  tff(f_34, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 3.13/1.84  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.13/1.84  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.84  tff(c_32, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_56, plain, (![A_29, B_30]: (k2_pre_topc(A_29, B_30)=B_30 | ~v4_pre_topc(B_30, A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.13/1.84  tff(c_65, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_56])).
% 3.13/1.84  tff(c_70, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65])).
% 3.13/1.84  tff(c_71, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_70])).
% 3.13/1.84  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_42, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_36, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_48, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 3.13/1.84  tff(c_122, plain, (![B_39, A_40]: (v4_pre_topc(B_39, A_40) | ~v3_pre_topc(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~v3_tdlat_3(A_40) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.13/1.84  tff(c_131, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_122])).
% 3.13/1.84  tff(c_136, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_48, c_131])).
% 3.13/1.84  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_136])).
% 3.13/1.84  tff(c_139, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 3.13/1.84  tff(c_145, plain, (![A_41, B_42]: (k2_pre_topc(A_41, B_42)=k2_struct_0(A_41) | ~v1_tops_1(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.13/1.84  tff(c_154, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_145])).
% 3.13/1.84  tff(c_159, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_139, c_154])).
% 3.13/1.84  tff(c_160, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_159])).
% 3.13/1.84  tff(c_34, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.13/1.84  tff(c_254, plain, (![B_59, A_60]: (v1_tops_1(B_59, A_60) | ~v3_tex_2(B_59, A_60) | ~v3_pre_topc(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.13/1.84  tff(c_263, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_254])).
% 3.13/1.84  tff(c_268, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_48, c_34, c_263])).
% 3.13/1.84  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_160, c_268])).
% 3.13/1.84  tff(c_271, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_159])).
% 3.13/1.84  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_struct_0(A_2), u1_struct_0(A_2)) | ~l1_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.13/1.84  tff(c_276, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_271, c_4])).
% 3.13/1.84  tff(c_280, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_276])).
% 3.13/1.84  tff(c_284, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_280])).
% 3.13/1.84  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_284])).
% 3.13/1.84  tff(c_290, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.13/1.84  tff(c_289, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.13/1.84  tff(c_365, plain, (![B_77, A_78]: (v3_pre_topc(B_77, A_78) | ~v4_pre_topc(B_77, A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~v3_tdlat_3(A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.13/1.84  tff(c_374, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_365])).
% 3.13/1.84  tff(c_379, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_289, c_374])).
% 3.13/1.84  tff(c_381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_379])).
% 3.13/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.84  
% 3.13/1.84  Inference rules
% 3.13/1.84  ----------------------
% 3.13/1.84  #Ref     : 0
% 3.13/1.84  #Sup     : 62
% 3.13/1.84  #Fact    : 0
% 3.13/1.84  #Define  : 0
% 3.13/1.84  #Split   : 5
% 3.13/1.84  #Chain   : 0
% 3.13/1.84  #Close   : 0
% 3.13/1.84  
% 3.13/1.84  Ordering : KBO
% 3.13/1.84  
% 3.13/1.84  Simplification rules
% 3.13/1.84  ----------------------
% 3.13/1.84  #Subsume      : 12
% 3.13/1.84  #Demod        : 47
% 3.13/1.84  #Tautology    : 18
% 3.13/1.84  #SimpNegUnit  : 7
% 3.13/1.84  #BackRed      : 0
% 3.13/1.84  
% 3.13/1.84  #Partial instantiations: 0
% 3.13/1.84  #Strategies tried      : 1
% 3.13/1.84  
% 3.13/1.84  Timing (in seconds)
% 3.13/1.84  ----------------------
% 3.13/1.84  Preprocessing        : 0.49
% 3.13/1.84  Parsing              : 0.25
% 3.13/1.84  CNF conversion       : 0.04
% 3.13/1.84  Main loop            : 0.40
% 3.13/1.85  Inferencing          : 0.18
% 3.13/1.85  Reduction            : 0.11
% 3.13/1.85  Demodulation         : 0.08
% 3.13/1.85  BG Simplification    : 0.02
% 3.13/1.85  Subsumption          : 0.05
% 3.13/1.85  Abstraction          : 0.03
% 3.13/1.85  MUC search           : 0.00
% 3.13/1.85  Cooper               : 0.00
% 3.13/1.85  Total                : 0.95
% 3.13/1.85  Index Insertion      : 0.00
% 3.13/1.85  Index Deletion       : 0.00
% 3.13/1.85  Index Matching       : 0.00
% 3.13/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
