%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:31 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 167 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   22
%              Number of atoms          :  187 ( 534 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & ~ v2_struct_0(B)
          & v7_struct_0(B)
          & v1_pre_topc(B)
          & v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc10_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & ~ v1_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tex_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_120,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_168,plain,(
    ! [A_67] :
      ( m1_pre_topc('#skF_1'(A_67),A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( l1_pre_topc(B_14)
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_172,plain,(
    ! [A_67] :
      ( l1_pre_topc('#skF_1'(A_67))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_168,c_20])).

tff(c_30,plain,(
    ! [A_19] :
      ( v2_pre_topc('#skF_1'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ! [A_19] :
      ( v7_struct_0('#skF_1'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_174,plain,(
    ! [A_69] :
      ( ~ v7_struct_0(A_69)
      | v1_tdlat_3(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_272,plain,(
    ! [A_90] :
      ( v1_tdlat_3('#skF_1'(A_90))
      | ~ v2_pre_topc('#skF_1'(A_90))
      | v2_struct_0('#skF_1'(A_90))
      | ~ l1_pre_topc('#skF_1'(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_34,c_174])).

tff(c_36,plain,(
    ! [A_19] :
      ( ~ v2_struct_0('#skF_1'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_277,plain,(
    ! [A_91] :
      ( v1_tdlat_3('#skF_1'(A_91))
      | ~ v2_pre_topc('#skF_1'(A_91))
      | ~ l1_pre_topc('#skF_1'(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_272,c_36])).

tff(c_281,plain,(
    ! [A_19] :
      ( v1_tdlat_3('#skF_1'(A_19))
      | ~ l1_pre_topc('#skF_1'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_30,c_277])).

tff(c_38,plain,(
    ! [A_19] :
      ( m1_pre_topc('#skF_1'(A_19),A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    ! [B_18,A_16] :
      ( m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_200,plain,(
    ! [B_76,A_77] :
      ( v2_tex_2(u1_struct_0(B_76),A_77)
      | ~ v1_tdlat_3(B_76)
      | ~ m1_subset_1(u1_struct_0(B_76),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc(B_76,A_77)
      | v2_struct_0(B_76)
      | ~ l1_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_207,plain,(
    ! [B_18,A_16] :
      ( v2_tex_2(u1_struct_0(B_18),A_16)
      | ~ v1_tdlat_3(B_18)
      | v2_struct_0(B_18)
      | v2_struct_0(A_16)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_28,c_200])).

tff(c_46,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_59,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_282,plain,(
    ! [C_92,A_93,B_94] :
      ( v2_tex_2(C_92,A_93)
      | ~ v2_tex_2(B_94,A_93)
      | ~ r1_tarski(C_92,B_94)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_290,plain,(
    ! [A_96,A_97] :
      ( v2_tex_2('#skF_3',A_96)
      | ~ v2_tex_2(A_97,A_96)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(A_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_65,c_282])).

tff(c_295,plain,(
    ! [A_97] :
      ( v2_tex_2('#skF_3','#skF_2')
      | ~ v2_tex_2(A_97,'#skF_2')
      | ~ m1_subset_1(A_97,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_290])).

tff(c_301,plain,(
    ! [A_97] :
      ( v2_tex_2('#skF_3','#skF_2')
      | ~ v2_tex_2(A_97,'#skF_2')
      | ~ m1_subset_1(A_97,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_295])).

tff(c_303,plain,(
    ! [A_98] :
      ( ~ v2_tex_2(A_98,'#skF_2')
      | ~ m1_subset_1(A_98,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_301])).

tff(c_307,plain,(
    ! [B_18] :
      ( ~ v2_tex_2(u1_struct_0(B_18),'#skF_2')
      | ~ m1_pre_topc(B_18,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_303])).

tff(c_333,plain,(
    ! [B_100] :
      ( ~ v2_tex_2(u1_struct_0(B_100),'#skF_2')
      | ~ m1_pre_topc(B_100,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_307])).

tff(c_337,plain,(
    ! [B_18] :
      ( ~ v1_tdlat_3(B_18)
      | v2_struct_0(B_18)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_18,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_207,c_333])).

tff(c_340,plain,(
    ! [B_18] :
      ( ~ v1_tdlat_3(B_18)
      | v2_struct_0(B_18)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_18,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_337])).

tff(c_342,plain,(
    ! [B_101] :
      ( ~ v1_tdlat_3(B_101)
      | v2_struct_0(B_101)
      | ~ m1_pre_topc(B_101,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_340])).

tff(c_346,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_1'('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_342])).

tff(c_349,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_346])).

tff(c_350,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_1'('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_349])).

tff(c_351,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_354,plain,
    ( ~ l1_pre_topc('#skF_1'('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_281,c_351])).

tff(c_357,plain,
    ( ~ l1_pre_topc('#skF_1'('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_354])).

tff(c_358,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_357])).

tff(c_361,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_172,c_358])).

tff(c_364,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_361])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_364])).

tff(c_367,plain,(
    v2_struct_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_371,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_367,c_36])).

tff(c_374,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_371])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:34:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.31  
% 2.59/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.32  %$ v2_tex_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.59/1.32  
% 2.59/1.32  %Foreground sorts:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Background operators:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Foreground operators:
% 2.59/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.32  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.59/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.32  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.59/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.59/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.32  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.59/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.59/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.59/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.32  
% 2.59/1.33  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.59/1.33  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((((m1_pre_topc(B, A) & ~v2_struct_0(B)) & v7_struct_0(B)) & v1_pre_topc(B)) & v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc10_tex_2)).
% 2.59/1.33  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.59/1.33  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v2_pre_topc(A)) & ~v1_tdlat_3(A)) => ((~v2_struct_0(A) & ~v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_tex_1)).
% 2.59/1.33  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l17_tex_2)).
% 2.59/1.33  tff(f_120, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.59/1.33  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 2.59/1.33  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.59/1.33  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 2.59/1.33  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.59/1.33  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.59/1.33  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.59/1.33  tff(c_168, plain, (![A_67]: (m1_pre_topc('#skF_1'(A_67), A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.59/1.33  tff(c_20, plain, (![B_14, A_12]: (l1_pre_topc(B_14) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.59/1.33  tff(c_172, plain, (![A_67]: (l1_pre_topc('#skF_1'(A_67)) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_168, c_20])).
% 2.59/1.33  tff(c_30, plain, (![A_19]: (v2_pre_topc('#skF_1'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.59/1.33  tff(c_34, plain, (![A_19]: (v7_struct_0('#skF_1'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.59/1.33  tff(c_174, plain, (![A_69]: (~v7_struct_0(A_69) | v1_tdlat_3(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.33  tff(c_272, plain, (![A_90]: (v1_tdlat_3('#skF_1'(A_90)) | ~v2_pre_topc('#skF_1'(A_90)) | v2_struct_0('#skF_1'(A_90)) | ~l1_pre_topc('#skF_1'(A_90)) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_34, c_174])).
% 2.59/1.33  tff(c_36, plain, (![A_19]: (~v2_struct_0('#skF_1'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.59/1.33  tff(c_277, plain, (![A_91]: (v1_tdlat_3('#skF_1'(A_91)) | ~v2_pre_topc('#skF_1'(A_91)) | ~l1_pre_topc('#skF_1'(A_91)) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_272, c_36])).
% 2.59/1.33  tff(c_281, plain, (![A_19]: (v1_tdlat_3('#skF_1'(A_19)) | ~l1_pre_topc('#skF_1'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(resolution, [status(thm)], [c_30, c_277])).
% 2.59/1.33  tff(c_38, plain, (![A_19]: (m1_pre_topc('#skF_1'(A_19), A_19) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.59/1.33  tff(c_28, plain, (![B_18, A_16]: (m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.59/1.33  tff(c_200, plain, (![B_76, A_77]: (v2_tex_2(u1_struct_0(B_76), A_77) | ~v1_tdlat_3(B_76) | ~m1_subset_1(u1_struct_0(B_76), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc(B_76, A_77) | v2_struct_0(B_76) | ~l1_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.59/1.33  tff(c_207, plain, (![B_18, A_16]: (v2_tex_2(u1_struct_0(B_18), A_16) | ~v1_tdlat_3(B_18) | v2_struct_0(B_18) | v2_struct_0(A_16) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_28, c_200])).
% 2.59/1.33  tff(c_46, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.59/1.33  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.59/1.33  tff(c_50, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.59/1.33  tff(c_59, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.33  tff(c_63, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_50, c_59])).
% 2.59/1.33  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.33  tff(c_65, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10])).
% 2.59/1.33  tff(c_282, plain, (![C_92, A_93, B_94]: (v2_tex_2(C_92, A_93) | ~v2_tex_2(B_94, A_93) | ~r1_tarski(C_92, B_94) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.33  tff(c_290, plain, (![A_96, A_97]: (v2_tex_2('#skF_3', A_96) | ~v2_tex_2(A_97, A_96) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(A_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_65, c_282])).
% 2.59/1.33  tff(c_295, plain, (![A_97]: (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(A_97, '#skF_2') | ~m1_subset_1(A_97, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_290])).
% 2.59/1.33  tff(c_301, plain, (![A_97]: (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(A_97, '#skF_2') | ~m1_subset_1(A_97, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_295])).
% 2.59/1.33  tff(c_303, plain, (![A_98]: (~v2_tex_2(A_98, '#skF_2') | ~m1_subset_1(A_98, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_301])).
% 2.59/1.33  tff(c_307, plain, (![B_18]: (~v2_tex_2(u1_struct_0(B_18), '#skF_2') | ~m1_pre_topc(B_18, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_303])).
% 2.59/1.33  tff(c_333, plain, (![B_100]: (~v2_tex_2(u1_struct_0(B_100), '#skF_2') | ~m1_pre_topc(B_100, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_307])).
% 2.59/1.33  tff(c_337, plain, (![B_18]: (~v1_tdlat_3(B_18) | v2_struct_0(B_18) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_18, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_207, c_333])).
% 2.59/1.33  tff(c_340, plain, (![B_18]: (~v1_tdlat_3(B_18) | v2_struct_0(B_18) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_18, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_337])).
% 2.59/1.33  tff(c_342, plain, (![B_101]: (~v1_tdlat_3(B_101) | v2_struct_0(B_101) | ~m1_pre_topc(B_101, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_340])).
% 2.59/1.33  tff(c_346, plain, (~v1_tdlat_3('#skF_1'('#skF_2')) | v2_struct_0('#skF_1'('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_342])).
% 2.59/1.33  tff(c_349, plain, (~v1_tdlat_3('#skF_1'('#skF_2')) | v2_struct_0('#skF_1'('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_346])).
% 2.59/1.33  tff(c_350, plain, (~v1_tdlat_3('#skF_1'('#skF_2')) | v2_struct_0('#skF_1'('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_349])).
% 2.59/1.33  tff(c_351, plain, (~v1_tdlat_3('#skF_1'('#skF_2'))), inference(splitLeft, [status(thm)], [c_350])).
% 2.59/1.33  tff(c_354, plain, (~l1_pre_topc('#skF_1'('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_281, c_351])).
% 2.59/1.33  tff(c_357, plain, (~l1_pre_topc('#skF_1'('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_354])).
% 2.59/1.33  tff(c_358, plain, (~l1_pre_topc('#skF_1'('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_357])).
% 2.59/1.33  tff(c_361, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_172, c_358])).
% 2.59/1.33  tff(c_364, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_361])).
% 2.59/1.33  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_364])).
% 2.59/1.33  tff(c_367, plain, (v2_struct_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_350])).
% 2.59/1.33  tff(c_371, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_367, c_36])).
% 2.59/1.33  tff(c_374, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_371])).
% 2.59/1.33  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_374])).
% 2.59/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  
% 2.59/1.33  Inference rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Ref     : 0
% 2.59/1.33  #Sup     : 64
% 2.59/1.33  #Fact    : 0
% 2.59/1.33  #Define  : 0
% 2.59/1.33  #Split   : 1
% 2.59/1.33  #Chain   : 0
% 2.59/1.33  #Close   : 0
% 2.59/1.33  
% 2.59/1.33  Ordering : KBO
% 2.59/1.33  
% 2.59/1.33  Simplification rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Subsume      : 11
% 2.59/1.33  #Demod        : 23
% 2.59/1.33  #Tautology    : 29
% 2.59/1.33  #SimpNegUnit  : 6
% 2.59/1.33  #BackRed      : 3
% 2.59/1.33  
% 2.59/1.33  #Partial instantiations: 0
% 2.59/1.33  #Strategies tried      : 1
% 2.59/1.33  
% 2.59/1.33  Timing (in seconds)
% 2.59/1.33  ----------------------
% 2.59/1.33  Preprocessing        : 0.31
% 2.59/1.33  Parsing              : 0.17
% 2.59/1.33  CNF conversion       : 0.02
% 2.59/1.33  Main loop            : 0.25
% 2.59/1.34  Inferencing          : 0.10
% 2.59/1.34  Reduction            : 0.07
% 2.59/1.34  Demodulation         : 0.05
% 2.59/1.34  BG Simplification    : 0.02
% 2.59/1.34  Subsumption          : 0.05
% 2.59/1.34  Abstraction          : 0.01
% 2.59/1.34  MUC search           : 0.00
% 2.59/1.34  Cooper               : 0.00
% 2.59/1.34  Total                : 0.60
% 2.59/1.34  Index Insertion      : 0.00
% 2.59/1.34  Index Deletion       : 0.00
% 2.59/1.34  Index Matching       : 0.00
% 2.59/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
