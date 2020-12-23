%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:19 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   88 (1217 expanded)
%              Number of leaves         :   28 ( 422 expanded)
%              Depth                    :   20
%              Number of atoms          :  175 (3890 expanded)
%              Number of equality atoms :   36 ( 585 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_49,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_51,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_30])).

tff(c_61,plain,(
    ! [A_38,B_39] :
      ( v1_pre_topc(k1_pre_topc(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [B_39] :
      ( v1_pre_topc(k1_pre_topc('#skF_2',B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_61])).

tff(c_72,plain,(
    ! [B_42] :
      ( v1_pre_topc(k1_pre_topc('#skF_2',B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_64])).

tff(c_76,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_51,c_72])).

tff(c_67,plain,(
    ! [A_40,B_41] :
      ( m1_pre_topc(k1_pre_topc(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    ! [B_41] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_41),'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_67])).

tff(c_77,plain,(
    ! [B_43] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_43),'#skF_2')
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_69])).

tff(c_81,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_77])).

tff(c_506,plain,(
    ! [A_99,B_100] :
      ( k2_struct_0(k1_pre_topc(A_99,B_100)) = B_100
      | ~ m1_pre_topc(k1_pre_topc(A_99,B_100),A_99)
      | ~ v1_pre_topc(k1_pre_topc(A_99,B_100))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_512,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_506])).

tff(c_519,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_51,c_49,c_76,c_512])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( l1_pre_topc(B_14)
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_14])).

tff(c_87,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_84])).

tff(c_44,plain,(
    ! [A_11] :
      ( u1_struct_0(A_11) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_91,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_87,c_44])).

tff(c_16,plain,(
    ! [A_15] :
      ( v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | ~ v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_100,plain,
    ( v1_xboole_0(k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_16])).

tff(c_109,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_110,plain,(
    ! [B_45,A_46] :
      ( u1_struct_0(B_45) = '#skF_1'(A_46,B_45)
      | v4_tex_2(B_45,A_46)
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [C_30] :
      ( u1_struct_0(C_30) != '#skF_3'
      | ~ v4_tex_2(C_30,'#skF_2')
      | ~ m1_pre_topc(C_30,'#skF_2')
      | ~ v1_pre_topc(C_30)
      | v2_struct_0(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_114,plain,(
    ! [B_45] :
      ( u1_struct_0(B_45) != '#skF_3'
      | ~ v1_pre_topc(B_45)
      | v2_struct_0(B_45)
      | u1_struct_0(B_45) = '#skF_1'('#skF_2',B_45)
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_110,c_26])).

tff(c_117,plain,(
    ! [B_45] :
      ( u1_struct_0(B_45) != '#skF_3'
      | ~ v1_pre_topc(B_45)
      | v2_struct_0(B_45)
      | u1_struct_0(B_45) = '#skF_1'('#skF_2',B_45)
      | ~ m1_pre_topc(B_45,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_114])).

tff(c_120,plain,(
    ! [B_49] :
      ( u1_struct_0(B_49) != '#skF_3'
      | ~ v1_pre_topc(B_49)
      | v2_struct_0(B_49)
      | u1_struct_0(B_49) = '#skF_1'('#skF_2',B_49)
      | ~ m1_pre_topc(B_49,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_117])).

tff(c_123,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_81,c_120])).

tff(c_126,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_76,c_91,c_123])).

tff(c_127,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_126])).

tff(c_128,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_271,plain,(
    ! [A_71,B_72] :
      ( k2_struct_0(k1_pre_topc(A_71,B_72)) = B_72
      | ~ m1_pre_topc(k1_pre_topc(A_71,B_72),A_71)
      | ~ v1_pre_topc(k1_pre_topc(A_71,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_277,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_271])).

tff(c_284,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_51,c_49,c_76,c_277])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_284])).

tff(c_288,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_290,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_91])).

tff(c_28,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_287,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_312,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_287])).

tff(c_20,plain,(
    ! [A_16,B_22] :
      ( ~ v3_tex_2('#skF_1'(A_16,B_22),A_16)
      | v4_tex_2(B_22,A_16)
      | ~ m1_pre_topc(B_22,A_16)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_316,plain,
    ( ~ v3_tex_2('#skF_3','#skF_2')
    | v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_20])).

tff(c_320,plain,
    ( v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_28,c_316])).

tff(c_321,plain,(
    v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_320])).

tff(c_325,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_321,c_26])).

tff(c_328,plain,(
    v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_81,c_290,c_325])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_328])).

tff(c_331,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v1_xboole_0(k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_333,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_336,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_333])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_336])).

tff(c_341,plain,(
    v1_xboole_0(k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_521,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_341])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.39  
% 2.72/1.39  %Foreground sorts:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Background operators:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Foreground operators:
% 2.72/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.72/1.39  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.39  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.72/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.72/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.72/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.72/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.72/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.72/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.72/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.72/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.72/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.39  
% 2.72/1.41  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 2.72/1.41  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.72/1.41  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.72/1.41  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.72/1.41  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 2.72/1.41  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.72/1.41  tff(f_68, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 2.72/1.41  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 2.72/1.41  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.41  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.41  tff(c_12, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.41  tff(c_40, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.41  tff(c_45, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.72/1.41  tff(c_49, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.72/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.41  tff(c_51, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_30])).
% 2.72/1.41  tff(c_61, plain, (![A_38, B_39]: (v1_pre_topc(k1_pre_topc(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.41  tff(c_64, plain, (![B_39]: (v1_pre_topc(k1_pre_topc('#skF_2', B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_61])).
% 2.72/1.41  tff(c_72, plain, (![B_42]: (v1_pre_topc(k1_pre_topc('#skF_2', B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_64])).
% 2.72/1.41  tff(c_76, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_51, c_72])).
% 2.72/1.41  tff(c_67, plain, (![A_40, B_41]: (m1_pre_topc(k1_pre_topc(A_40, B_41), A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.41  tff(c_69, plain, (![B_41]: (m1_pre_topc(k1_pre_topc('#skF_2', B_41), '#skF_2') | ~m1_subset_1(B_41, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_67])).
% 2.72/1.41  tff(c_77, plain, (![B_43]: (m1_pre_topc(k1_pre_topc('#skF_2', B_43), '#skF_2') | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_69])).
% 2.72/1.41  tff(c_81, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_51, c_77])).
% 2.72/1.41  tff(c_506, plain, (![A_99, B_100]: (k2_struct_0(k1_pre_topc(A_99, B_100))=B_100 | ~m1_pre_topc(k1_pre_topc(A_99, B_100), A_99) | ~v1_pre_topc(k1_pre_topc(A_99, B_100)) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.41  tff(c_512, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_81, c_506])).
% 2.72/1.41  tff(c_519, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_51, c_49, c_76, c_512])).
% 2.72/1.41  tff(c_14, plain, (![B_14, A_12]: (l1_pre_topc(B_14) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.41  tff(c_84, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_81, c_14])).
% 2.72/1.41  tff(c_87, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_84])).
% 2.72/1.41  tff(c_44, plain, (![A_11]: (u1_struct_0(A_11)=k2_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.72/1.41  tff(c_91, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_87, c_44])).
% 2.72/1.41  tff(c_16, plain, (![A_15]: (v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | ~v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.41  tff(c_100, plain, (v1_xboole_0(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_16])).
% 2.72/1.41  tff(c_109, plain, (~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_100])).
% 2.72/1.41  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.41  tff(c_110, plain, (![B_45, A_46]: (u1_struct_0(B_45)='#skF_1'(A_46, B_45) | v4_tex_2(B_45, A_46) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.41  tff(c_26, plain, (![C_30]: (u1_struct_0(C_30)!='#skF_3' | ~v4_tex_2(C_30, '#skF_2') | ~m1_pre_topc(C_30, '#skF_2') | ~v1_pre_topc(C_30) | v2_struct_0(C_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.41  tff(c_114, plain, (![B_45]: (u1_struct_0(B_45)!='#skF_3' | ~v1_pre_topc(B_45) | v2_struct_0(B_45) | u1_struct_0(B_45)='#skF_1'('#skF_2', B_45) | ~m1_pre_topc(B_45, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_110, c_26])).
% 2.72/1.41  tff(c_117, plain, (![B_45]: (u1_struct_0(B_45)!='#skF_3' | ~v1_pre_topc(B_45) | v2_struct_0(B_45) | u1_struct_0(B_45)='#skF_1'('#skF_2', B_45) | ~m1_pre_topc(B_45, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_114])).
% 2.72/1.41  tff(c_120, plain, (![B_49]: (u1_struct_0(B_49)!='#skF_3' | ~v1_pre_topc(B_49) | v2_struct_0(B_49) | u1_struct_0(B_49)='#skF_1'('#skF_2', B_49) | ~m1_pre_topc(B_49, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_117])).
% 2.72/1.41  tff(c_123, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_81, c_120])).
% 2.72/1.41  tff(c_126, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_76, c_91, c_123])).
% 2.72/1.41  tff(c_127, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_109, c_126])).
% 2.72/1.41  tff(c_128, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_127])).
% 2.72/1.41  tff(c_271, plain, (![A_71, B_72]: (k2_struct_0(k1_pre_topc(A_71, B_72))=B_72 | ~m1_pre_topc(k1_pre_topc(A_71, B_72), A_71) | ~v1_pre_topc(k1_pre_topc(A_71, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.41  tff(c_277, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_81, c_271])).
% 2.72/1.41  tff(c_284, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_51, c_49, c_76, c_277])).
% 2.72/1.41  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_284])).
% 2.72/1.41  tff(c_288, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_127])).
% 2.72/1.41  tff(c_290, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_91])).
% 2.72/1.41  tff(c_28, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.41  tff(c_287, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_127])).
% 2.72/1.41  tff(c_312, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_287])).
% 2.72/1.41  tff(c_20, plain, (![A_16, B_22]: (~v3_tex_2('#skF_1'(A_16, B_22), A_16) | v4_tex_2(B_22, A_16) | ~m1_pre_topc(B_22, A_16) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.41  tff(c_316, plain, (~v3_tex_2('#skF_3', '#skF_2') | v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_312, c_20])).
% 2.72/1.41  tff(c_320, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_28, c_316])).
% 2.72/1.41  tff(c_321, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_320])).
% 2.72/1.41  tff(c_325, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_321, c_26])).
% 2.72/1.41  tff(c_328, plain, (v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_81, c_290, c_325])).
% 2.72/1.41  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_328])).
% 2.72/1.41  tff(c_331, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v1_xboole_0(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_100])).
% 2.72/1.41  tff(c_333, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_331])).
% 2.72/1.41  tff(c_336, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_333])).
% 2.72/1.41  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_336])).
% 2.72/1.41  tff(c_341, plain, (v1_xboole_0(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_331])).
% 2.72/1.41  tff(c_521, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_341])).
% 2.72/1.41  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_521])).
% 2.72/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  Inference rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Ref     : 0
% 2.72/1.41  #Sup     : 99
% 2.72/1.41  #Fact    : 0
% 2.72/1.41  #Define  : 0
% 2.72/1.41  #Split   : 4
% 2.72/1.41  #Chain   : 0
% 2.72/1.41  #Close   : 0
% 2.72/1.41  
% 2.72/1.41  Ordering : KBO
% 2.72/1.41  
% 2.72/1.41  Simplification rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Subsume      : 3
% 2.72/1.41  #Demod        : 72
% 2.72/1.41  #Tautology    : 18
% 2.72/1.41  #SimpNegUnit  : 16
% 2.72/1.41  #BackRed      : 7
% 2.72/1.41  
% 2.72/1.41  #Partial instantiations: 0
% 2.72/1.41  #Strategies tried      : 1
% 2.72/1.41  
% 2.72/1.41  Timing (in seconds)
% 2.72/1.41  ----------------------
% 2.72/1.41  Preprocessing        : 0.31
% 2.72/1.41  Parsing              : 0.16
% 2.72/1.41  CNF conversion       : 0.02
% 2.72/1.41  Main loop            : 0.33
% 2.72/1.41  Inferencing          : 0.12
% 2.72/1.41  Reduction            : 0.10
% 2.72/1.41  Demodulation         : 0.07
% 2.72/1.41  BG Simplification    : 0.02
% 2.72/1.41  Subsumption          : 0.07
% 2.72/1.41  Abstraction          : 0.02
% 2.72/1.41  MUC search           : 0.00
% 2.72/1.41  Cooper               : 0.00
% 2.72/1.41  Total                : 0.68
% 2.72/1.41  Index Insertion      : 0.00
% 2.72/1.41  Index Deletion       : 0.00
% 2.72/1.41  Index Matching       : 0.00
% 2.72/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
