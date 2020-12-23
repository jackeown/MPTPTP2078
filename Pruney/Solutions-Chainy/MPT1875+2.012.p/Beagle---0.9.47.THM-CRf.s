%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:48 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 112 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 329 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k1_pre_topc(A,B))
        & v1_pre_topc(k1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_28,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_84,plain,(
    ! [A_36,B_37] :
      ( m1_pre_topc(k1_pre_topc(A_36,B_37),A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_94,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90])).

tff(c_190,plain,(
    ! [A_51,B_52] :
      ( ~ v2_struct_0(k1_pre_topc(A_51,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | v1_xboole_0(B_52)
      | ~ l1_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_205,plain,
    ( ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_190])).

tff(c_210,plain,
    ( ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_205])).

tff(c_211,plain,
    ( ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_210])).

tff(c_212,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_34,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_14,plain,(
    ! [B_11,A_9] :
      ( v1_tdlat_3(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v1_tdlat_3(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_14])).

tff(c_104,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_98])).

tff(c_105,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_104])).

tff(c_53,plain,(
    ! [A_33,B_34] :
      ( u1_struct_0(k1_pre_topc(A_33,B_34)) = B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_59,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_63,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( m1_subset_1(u1_struct_0(B_14),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_277,plain,(
    ! [B_63,A_64] :
      ( v2_tex_2(u1_struct_0(B_63),A_64)
      | ~ v1_tdlat_3(B_63)
      | ~ m1_subset_1(u1_struct_0(B_63),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_pre_topc(B_63,A_64)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_298,plain,(
    ! [B_65,A_66] :
      ( v2_tex_2(u1_struct_0(B_65),A_66)
      | ~ v1_tdlat_3(B_65)
      | v2_struct_0(B_65)
      | v2_struct_0(A_66)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_20,c_277])).

tff(c_304,plain,(
    ! [A_66] :
      ( v2_tex_2('#skF_2',A_66)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | v2_struct_0(A_66)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_298])).

tff(c_306,plain,(
    ! [A_66] :
      ( v2_tex_2('#skF_2',A_66)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | v2_struct_0(A_66)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_304])).

tff(c_308,plain,(
    ! [A_67] :
      ( v2_tex_2('#skF_2',A_67)
      | v2_struct_0(A_67)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_306])).

tff(c_311,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_308])).

tff(c_314,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_311])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_28,c_314])).

tff(c_317,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_328,plain,(
    ! [B_70,A_71] :
      ( v2_tex_2(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ v1_xboole_0(B_70)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_343,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v1_xboole_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_328])).

tff(c_351,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_317,c_343])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_28,c_351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:51:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.77  
% 2.85/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.77  %$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.17/1.77  
% 3.17/1.77  %Foreground sorts:
% 3.17/1.77  
% 3.17/1.77  
% 3.17/1.77  %Background operators:
% 3.17/1.77  
% 3.17/1.77  
% 3.17/1.77  %Foreground operators:
% 3.17/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.17/1.77  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 3.17/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.17/1.77  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.17/1.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.17/1.77  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.77  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.77  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.17/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.77  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.17/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.77  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.17/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.17/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.77  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.17/1.77  
% 3.23/1.79  tff(f_135, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 3.23/1.79  tff(f_33, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 3.23/1.79  tff(f_48, axiom, (![A, B]: ((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (~v2_struct_0(k1_pre_topc(A, B)) & v1_pre_topc(k1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_pre_topc)).
% 3.23/1.79  tff(f_79, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 3.23/1.79  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 3.23/1.79  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 3.23/1.79  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 3.23/1.79  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.23/1.79  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.23/1.79  tff(c_28, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.23/1.79  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.23/1.79  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.23/1.79  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.23/1.79  tff(c_84, plain, (![A_36, B_37]: (m1_pre_topc(k1_pre_topc(A_36, B_37), A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.79  tff(c_90, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_84])).
% 3.23/1.79  tff(c_94, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_90])).
% 3.23/1.79  tff(c_190, plain, (![A_51, B_52]: (~v2_struct_0(k1_pre_topc(A_51, B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | v1_xboole_0(B_52) | ~l1_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.79  tff(c_205, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v1_xboole_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_190])).
% 3.23/1.79  tff(c_210, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_205])).
% 3.23/1.79  tff(c_211, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_210])).
% 3.23/1.79  tff(c_212, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_211])).
% 3.23/1.79  tff(c_34, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.23/1.79  tff(c_14, plain, (![B_11, A_9]: (v1_tdlat_3(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9) | ~v1_tdlat_3(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.80  tff(c_98, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_94, c_14])).
% 3.23/1.80  tff(c_104, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_98])).
% 3.23/1.80  tff(c_105, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_104])).
% 3.23/1.80  tff(c_53, plain, (![A_33, B_34]: (u1_struct_0(k1_pre_topc(A_33, B_34))=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.80  tff(c_59, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_53])).
% 3.23/1.80  tff(c_63, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_59])).
% 3.23/1.80  tff(c_20, plain, (![B_14, A_12]: (m1_subset_1(u1_struct_0(B_14), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.23/1.80  tff(c_277, plain, (![B_63, A_64]: (v2_tex_2(u1_struct_0(B_63), A_64) | ~v1_tdlat_3(B_63) | ~m1_subset_1(u1_struct_0(B_63), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_pre_topc(B_63, A_64) | v2_struct_0(B_63) | ~l1_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.23/1.80  tff(c_298, plain, (![B_65, A_66]: (v2_tex_2(u1_struct_0(B_65), A_66) | ~v1_tdlat_3(B_65) | v2_struct_0(B_65) | v2_struct_0(A_66) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_20, c_277])).
% 3.23/1.80  tff(c_304, plain, (![A_66]: (v2_tex_2('#skF_2', A_66) | ~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(A_66) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_66) | ~l1_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_63, c_298])).
% 3.23/1.80  tff(c_306, plain, (![A_66]: (v2_tex_2('#skF_2', A_66) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(A_66) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_66) | ~l1_pre_topc(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_304])).
% 3.23/1.80  tff(c_308, plain, (![A_67]: (v2_tex_2('#skF_2', A_67) | v2_struct_0(A_67) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_67) | ~l1_pre_topc(A_67))), inference(negUnitSimplification, [status(thm)], [c_212, c_306])).
% 3.23/1.80  tff(c_311, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_94, c_308])).
% 3.23/1.80  tff(c_314, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_311])).
% 3.23/1.80  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_28, c_314])).
% 3.23/1.80  tff(c_317, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_211])).
% 3.23/1.80  tff(c_328, plain, (![B_70, A_71]: (v2_tex_2(B_70, A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~v1_xboole_0(B_70) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.80  tff(c_343, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v1_xboole_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_328])).
% 3.23/1.80  tff(c_351, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_317, c_343])).
% 3.23/1.80  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_28, c_351])).
% 3.23/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.80  
% 3.23/1.80  Inference rules
% 3.23/1.80  ----------------------
% 3.23/1.80  #Ref     : 0
% 3.23/1.80  #Sup     : 70
% 3.23/1.80  #Fact    : 0
% 3.23/1.80  #Define  : 0
% 3.23/1.80  #Split   : 2
% 3.23/1.80  #Chain   : 0
% 3.23/1.80  #Close   : 0
% 3.23/1.80  
% 3.23/1.80  Ordering : KBO
% 3.23/1.80  
% 3.23/1.80  Simplification rules
% 3.23/1.80  ----------------------
% 3.23/1.80  #Subsume      : 19
% 3.23/1.80  #Demod        : 35
% 3.23/1.80  #Tautology    : 10
% 3.23/1.80  #SimpNegUnit  : 13
% 3.23/1.80  #BackRed      : 0
% 3.23/1.80  
% 3.23/1.80  #Partial instantiations: 0
% 3.23/1.80  #Strategies tried      : 1
% 3.23/1.80  
% 3.23/1.80  Timing (in seconds)
% 3.23/1.80  ----------------------
% 3.23/1.80  Preprocessing        : 0.50
% 3.23/1.80  Parsing              : 0.27
% 3.23/1.80  CNF conversion       : 0.03
% 3.23/1.80  Main loop            : 0.44
% 3.23/1.80  Inferencing          : 0.17
% 3.23/1.80  Reduction            : 0.12
% 3.23/1.80  Demodulation         : 0.08
% 3.23/1.80  BG Simplification    : 0.03
% 3.23/1.80  Subsumption          : 0.09
% 3.23/1.80  Abstraction          : 0.02
% 3.23/1.80  MUC search           : 0.00
% 3.23/1.80  Cooper               : 0.00
% 3.23/1.80  Total                : 0.99
% 3.23/1.80  Index Insertion      : 0.00
% 3.23/1.80  Index Deletion       : 0.00
% 3.23/1.80  Index Matching       : 0.00
% 3.23/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
