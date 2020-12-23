%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:22 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 311 expanded)
%              Number of leaves         :   25 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  183 ( 943 expanded)
%              Number of equality atoms :   39 ( 106 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v4_pre_topc(B,A) )
             => ( v5_tops_1(B,A)
              <=> v6_tops_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_44,axiom,(
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
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_15),B_17),A_15)
      | ~ v4_pre_topc(B_17,A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,
    ( ~ v6_tops_1('#skF_2','#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_41,plain,(
    ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( k2_pre_topc(A_24,B_25) = B_25
      | ~ v4_pre_topc(B_25,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_55,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_51])).

tff(c_40,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_40])).

tff(c_89,plain,(
    ! [A_36,B_37] :
      ( k1_tops_1(A_36,k2_pre_topc(A_36,B_37)) = B_37
      | ~ v6_tops_1(B_37,A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_98,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42,c_55,c_94])).

tff(c_113,plain,(
    ! [B_42,A_43] :
      ( v5_tops_1(B_42,A_43)
      | k2_pre_topc(A_43,k1_tops_1(A_43,B_42)) != B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_113])).

tff(c_117,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_55,c_115])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_117])).

tff(c_120,plain,(
    ~ v6_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_125,plain,(
    ! [A_46,B_47] :
      ( k2_pre_topc(A_46,B_47) = B_47
      | ~ v4_pre_topc(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_132,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_125])).

tff(c_136,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_132])).

tff(c_184,plain,(
    ! [B_58,A_59] :
      ( v6_tops_1(B_58,A_59)
      | k1_tops_1(A_59,k2_pre_topc(A_59,B_58)) != B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_188,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_184])).

tff(c_193,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_188])).

tff(c_194,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_193])).

tff(c_121,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_164,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,k1_tops_1(A_54,B_55)) = B_55
      | ~ v5_tops_1(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_169,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_164])).

tff(c_173,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_121,c_169])).

tff(c_186,plain,
    ( v6_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_184])).

tff(c_191,plain,
    ( v6_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_186])).

tff(c_195,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_28,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [A_18,B_20] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_18),B_20),A_18)
      | ~ v3_pre_topc(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_237,plain,(
    ! [A_68,B_69] :
      ( k2_pre_topc(A_68,k3_subset_1(u1_struct_0(A_68),B_69)) = k3_subset_1(u1_struct_0(A_68),B_69)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_68),B_69),A_68)
      | ~ l1_pre_topc(A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68))) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_245,plain,(
    ! [A_70,B_71] :
      ( k2_pre_topc(A_70,k3_subset_1(u1_struct_0(A_70),B_71)) = k3_subset_1(u1_struct_0(A_70),B_71)
      | ~ v3_pre_topc(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_24,c_237])).

tff(c_250,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_245])).

tff(c_254,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_250])).

tff(c_8,plain,(
    ! [A_6,B_8] :
      ( k3_subset_1(u1_struct_0(A_6),k2_pre_topc(A_6,k3_subset_1(u1_struct_0(A_6),B_8))) = k1_tops_1(A_6,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_258,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_8])).

tff(c_264,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_258])).

tff(c_289,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_2])).

tff(c_305,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_289])).

tff(c_309,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_305])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_309])).

tff(c_315,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_6,plain,(
    ! [A_3,B_5] :
      ( k2_pre_topc(A_3,B_5) = B_5
      | ~ v4_pre_topc(B_5,A_3)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_326,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_315,c_6])).

tff(c_338,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_173,c_326])).

tff(c_339,plain,(
    ~ v4_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_338])).

tff(c_381,plain,(
    ! [A_80,B_81] :
      ( k2_pre_topc(A_80,k3_subset_1(u1_struct_0(A_80),B_81)) = k3_subset_1(u1_struct_0(A_80),B_81)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_80),B_81),A_80)
      | ~ l1_pre_topc(A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80))) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_393,plain,(
    ! [A_84,B_85] :
      ( k2_pre_topc(A_84,k3_subset_1(u1_struct_0(A_84),B_85)) = k3_subset_1(u1_struct_0(A_84),B_85)
      | ~ v3_pre_topc(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_24,c_381])).

tff(c_400,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_393])).

tff(c_407,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_400])).

tff(c_414,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_8])).

tff(c_422,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_414])).

tff(c_447,plain,
    ( v4_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_24])).

tff(c_467,plain,
    ( v4_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_447])).

tff(c_468,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_467])).

tff(c_471,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_468])).

tff(c_474,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_471])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_474])).

tff(c_479,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_483,plain,
    ( ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_479])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.46  
% 2.43/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.46  %$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.43/1.46  
% 2.43/1.46  %Foreground sorts:
% 2.43/1.46  
% 2.43/1.46  
% 2.43/1.46  %Background operators:
% 2.43/1.46  
% 2.43/1.46  
% 2.43/1.46  %Foreground operators:
% 2.43/1.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.43/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.46  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 2.43/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.43/1.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.43/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.43/1.46  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.43/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.43/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.43/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.46  
% 2.59/1.48  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v4_pre_topc(B, A)) => (v5_tops_1(B, A) <=> v6_tops_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tops_1)).
% 2.59/1.48  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.59/1.48  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.59/1.48  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.59/1.48  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 2.59/1.48  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 2.59/1.48  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 2.59/1.48  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.59/1.48  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.48  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.48  tff(c_26, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.48  tff(c_20, plain, (![A_15, B_17]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_15), B_17), A_15) | ~v4_pre_topc(B_17, A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.48  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.48  tff(c_34, plain, (~v6_tops_1('#skF_2', '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.48  tff(c_41, plain, (~v5_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.59/1.48  tff(c_44, plain, (![A_24, B_25]: (k2_pre_topc(A_24, B_25)=B_25 | ~v4_pre_topc(B_25, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.48  tff(c_51, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.59/1.48  tff(c_55, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_51])).
% 2.59/1.48  tff(c_40, plain, (v5_tops_1('#skF_2', '#skF_1') | v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.48  tff(c_42, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41, c_40])).
% 2.59/1.48  tff(c_89, plain, (![A_36, B_37]: (k1_tops_1(A_36, k2_pre_topc(A_36, B_37))=B_37 | ~v6_tops_1(B_37, A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.48  tff(c_94, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_89])).
% 2.59/1.48  tff(c_98, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42, c_55, c_94])).
% 2.59/1.48  tff(c_113, plain, (![B_42, A_43]: (v5_tops_1(B_42, A_43) | k2_pre_topc(A_43, k1_tops_1(A_43, B_42))!=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.48  tff(c_115, plain, (v5_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_98, c_113])).
% 2.59/1.48  tff(c_117, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_55, c_115])).
% 2.59/1.48  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_117])).
% 2.59/1.48  tff(c_120, plain, (~v6_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.59/1.48  tff(c_125, plain, (![A_46, B_47]: (k2_pre_topc(A_46, B_47)=B_47 | ~v4_pre_topc(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.48  tff(c_132, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_125])).
% 2.59/1.48  tff(c_136, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_132])).
% 2.59/1.48  tff(c_184, plain, (![B_58, A_59]: (v6_tops_1(B_58, A_59) | k1_tops_1(A_59, k2_pre_topc(A_59, B_58))!=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.48  tff(c_188, plain, (v6_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_136, c_184])).
% 2.59/1.48  tff(c_193, plain, (v6_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_188])).
% 2.59/1.48  tff(c_194, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_120, c_193])).
% 2.59/1.48  tff(c_121, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.59/1.48  tff(c_164, plain, (![A_54, B_55]: (k2_pre_topc(A_54, k1_tops_1(A_54, B_55))=B_55 | ~v5_tops_1(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.48  tff(c_169, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_164])).
% 2.59/1.48  tff(c_173, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_121, c_169])).
% 2.59/1.48  tff(c_186, plain, (v6_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_173, c_184])).
% 2.59/1.48  tff(c_191, plain, (v6_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_186])).
% 2.59/1.48  tff(c_195, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_191])).
% 2.59/1.48  tff(c_28, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.48  tff(c_24, plain, (![A_18, B_20]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_18), B_20), A_18) | ~v3_pre_topc(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.59/1.48  tff(c_237, plain, (![A_68, B_69]: (k2_pre_topc(A_68, k3_subset_1(u1_struct_0(A_68), B_69))=k3_subset_1(u1_struct_0(A_68), B_69) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_68), B_69), A_68) | ~l1_pre_topc(A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))))), inference(resolution, [status(thm)], [c_2, c_125])).
% 2.59/1.48  tff(c_245, plain, (![A_70, B_71]: (k2_pre_topc(A_70, k3_subset_1(u1_struct_0(A_70), B_71))=k3_subset_1(u1_struct_0(A_70), B_71) | ~v3_pre_topc(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_24, c_237])).
% 2.59/1.48  tff(c_250, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_245])).
% 2.59/1.48  tff(c_254, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_250])).
% 2.59/1.48  tff(c_8, plain, (![A_6, B_8]: (k3_subset_1(u1_struct_0(A_6), k2_pre_topc(A_6, k3_subset_1(u1_struct_0(A_6), B_8)))=k1_tops_1(A_6, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.48  tff(c_258, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_254, c_8])).
% 2.59/1.48  tff(c_264, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_258])).
% 2.59/1.48  tff(c_289, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_264, c_2])).
% 2.59/1.48  tff(c_305, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_195, c_289])).
% 2.59/1.48  tff(c_309, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_305])).
% 2.59/1.48  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_309])).
% 2.59/1.48  tff(c_315, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_191])).
% 2.59/1.48  tff(c_6, plain, (![A_3, B_5]: (k2_pre_topc(A_3, B_5)=B_5 | ~v4_pre_topc(B_5, A_3) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.48  tff(c_326, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_315, c_6])).
% 2.59/1.48  tff(c_338, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_173, c_326])).
% 2.59/1.48  tff(c_339, plain, (~v4_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_194, c_338])).
% 2.59/1.48  tff(c_381, plain, (![A_80, B_81]: (k2_pre_topc(A_80, k3_subset_1(u1_struct_0(A_80), B_81))=k3_subset_1(u1_struct_0(A_80), B_81) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_80), B_81), A_80) | ~l1_pre_topc(A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))))), inference(resolution, [status(thm)], [c_2, c_125])).
% 2.59/1.48  tff(c_393, plain, (![A_84, B_85]: (k2_pre_topc(A_84, k3_subset_1(u1_struct_0(A_84), B_85))=k3_subset_1(u1_struct_0(A_84), B_85) | ~v3_pre_topc(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_24, c_381])).
% 2.59/1.48  tff(c_400, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_393])).
% 2.59/1.48  tff(c_407, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_400])).
% 2.59/1.48  tff(c_414, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_407, c_8])).
% 2.59/1.48  tff(c_422, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_414])).
% 2.59/1.48  tff(c_447, plain, (v4_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_422, c_24])).
% 2.59/1.48  tff(c_467, plain, (v4_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_447])).
% 2.59/1.48  tff(c_468, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_339, c_467])).
% 2.59/1.48  tff(c_471, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_468])).
% 2.59/1.48  tff(c_474, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_471])).
% 2.59/1.48  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_474])).
% 2.59/1.48  tff(c_479, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_468])).
% 2.59/1.48  tff(c_483, plain, (~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_479])).
% 2.59/1.48  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_483])).
% 2.59/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.48  
% 2.59/1.48  Inference rules
% 2.59/1.48  ----------------------
% 2.59/1.48  #Ref     : 0
% 2.59/1.48  #Sup     : 98
% 2.59/1.48  #Fact    : 0
% 2.59/1.48  #Define  : 0
% 2.59/1.48  #Split   : 4
% 2.59/1.48  #Chain   : 0
% 2.59/1.48  #Close   : 0
% 2.59/1.48  
% 2.59/1.48  Ordering : KBO
% 2.59/1.48  
% 2.59/1.48  Simplification rules
% 2.59/1.48  ----------------------
% 2.59/1.48  #Subsume      : 5
% 2.59/1.48  #Demod        : 82
% 2.59/1.48  #Tautology    : 36
% 2.59/1.48  #SimpNegUnit  : 9
% 2.59/1.48  #BackRed      : 0
% 2.59/1.48  
% 2.59/1.48  #Partial instantiations: 0
% 2.59/1.48  #Strategies tried      : 1
% 2.59/1.48  
% 2.59/1.48  Timing (in seconds)
% 2.59/1.48  ----------------------
% 2.59/1.49  Preprocessing        : 0.29
% 2.59/1.49  Parsing              : 0.15
% 2.59/1.49  CNF conversion       : 0.02
% 2.59/1.49  Main loop            : 0.27
% 2.59/1.49  Inferencing          : 0.10
% 2.59/1.49  Reduction            : 0.08
% 2.59/1.49  Demodulation         : 0.05
% 2.59/1.49  BG Simplification    : 0.02
% 2.59/1.49  Subsumption          : 0.05
% 2.59/1.49  Abstraction          : 0.01
% 2.59/1.49  MUC search           : 0.00
% 2.59/1.49  Cooper               : 0.00
% 2.59/1.49  Total                : 0.61
% 2.59/1.49  Index Insertion      : 0.00
% 2.59/1.49  Index Deletion       : 0.00
% 2.59/1.49  Index Matching       : 0.00
% 2.59/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
