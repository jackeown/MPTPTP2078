%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:50 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 559 expanded)
%              Number of leaves         :   32 ( 211 expanded)
%              Depth                    :   16
%              Number of atoms          :  374 (2255 expanded)
%              Number of equality atoms :   14 (  72 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) )
       => ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).

tff(f_164,axiom,(
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

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B)
              & v2_tdlat_3(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_538,plain,(
    ! [A_97,B_98] :
      ( m1_pre_topc('#skF_1'(A_97,B_98),A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | v1_xboole_0(B_98)
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_540,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_538])).

tff(c_543,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_540])).

tff(c_544,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_543])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_556,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_544,c_6])).

tff(c_570,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_556])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_62,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_65,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54])).

tff(c_274,plain,(
    ! [A_61,B_62] :
      ( m1_pre_topc('#skF_1'(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | v1_xboole_0(B_62)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_278,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_274])).

tff(c_284,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_278])).

tff(c_285,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_284])).

tff(c_118,plain,(
    ! [A_51,B_52] :
      ( ~ v2_struct_0('#skF_1'(A_51,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | v1_xboole_0(B_52)
      | ~ l1_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_121,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_118])).

tff(c_124,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_121])).

tff(c_125,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_124])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_294,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_285,c_2])).

tff(c_308,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_294])).

tff(c_126,plain,(
    ! [A_53,B_54] :
      ( u1_struct_0('#skF_1'(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_xboole_0(B_54)
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_129,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_126])).

tff(c_132,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_133,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_132])).

tff(c_36,plain,(
    ! [A_19,B_23] :
      ( ~ v2_struct_0('#skF_1'(A_19,B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | v1_xboole_0(B_23)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_140,plain,(
    ! [B_23] :
      ( ~ v2_struct_0('#skF_1'('#skF_1'('#skF_2','#skF_3'),B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1('#skF_3'))
      | v1_xboole_0(B_23)
      | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
      | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_36])).

tff(c_153,plain,(
    ! [B_23] :
      ( ~ v2_struct_0('#skF_1'('#skF_1'('#skF_2','#skF_3'),B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1('#skF_3'))
      | v1_xboole_0(B_23)
      | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_140])).

tff(c_164,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_165,plain,(
    ! [A_55,B_56] :
      ( m1_pre_topc('#skF_1'(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | v1_xboole_0(B_56)
      | ~ l1_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_169,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_165])).

tff(c_173,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_169])).

tff(c_174,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_173])).

tff(c_186,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_200,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_186])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_200])).

tff(c_204,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_8])).

tff(c_156,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_146])).

tff(c_159,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_163,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_163])).

tff(c_219,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | ~ v7_struct_0(A_11)
      | v2_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_223,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_219,c_16])).

tff(c_229,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_223])).

tff(c_233,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_234,plain,(
    ! [A_59,B_60] :
      ( m1_pre_topc('#skF_1'(A_59,B_60),A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | v1_xboole_0(B_60)
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_238,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_234])).

tff(c_242,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_238])).

tff(c_243,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_242])).

tff(c_255,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_243,c_6])).

tff(c_269,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_255])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_269])).

tff(c_272,plain,
    ( ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_322,plain,(
    v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_272])).

tff(c_436,plain,(
    ! [B_75,A_76] :
      ( v2_tex_2(u1_struct_0(B_75),A_76)
      | ~ v1_tdlat_3(B_75)
      | ~ m1_subset_1(u1_struct_0(B_75),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_75,A_76)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_445,plain,(
    ! [A_76] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_76)
      | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_76)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_436])).

tff(c_450,plain,(
    ! [A_76] :
      ( v2_tex_2('#skF_3',A_76)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_76)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_133,c_445])).

tff(c_455,plain,(
    ! [A_77] :
      ( v2_tex_2('#skF_3',A_77)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_77)
      | ~ l1_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_450])).

tff(c_464,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_455])).

tff(c_470,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_285,c_464])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_65,c_470])).

tff(c_474,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_473,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_530,plain,(
    ! [A_95,B_96] :
      ( ~ v2_struct_0('#skF_1'(A_95,B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_96)
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_533,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_530])).

tff(c_536,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_533])).

tff(c_537,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_536])).

tff(c_48,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_28,plain,(
    ! [B_18,A_16] :
      ( v2_tdlat_3(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_tdlat_3(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_550,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_544,c_28])).

tff(c_563,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_550])).

tff(c_564,plain,(
    v2_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_563])).

tff(c_22,plain,(
    ! [B_14,A_12] :
      ( ~ v1_tdlat_3(B_14)
      | ~ v2_tdlat_3(B_14)
      | v7_struct_0(B_14)
      | v2_struct_0(B_14)
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_547,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_544,c_22])).

tff(c_559,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_547])).

tff(c_560,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_537,c_559])).

tff(c_576,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_560])).

tff(c_577,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_580,plain,(
    ! [A_99,B_100] :
      ( u1_struct_0('#skF_1'(A_99,B_100)) = B_100
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | v1_xboole_0(B_100)
      | ~ l1_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_583,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_580])).

tff(c_586,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_583])).

tff(c_587,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_586])).

tff(c_622,plain,(
    ! [B_101,A_102] :
      ( v1_tdlat_3(B_101)
      | ~ v2_tex_2(u1_struct_0(B_101),A_102)
      | ~ m1_subset_1(u1_struct_0(B_101),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc(B_101,A_102)
      | v2_struct_0(B_101)
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_625,plain,(
    ! [A_102] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_102)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_102)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_622])).

tff(c_629,plain,(
    ! [A_102] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2('#skF_3',A_102)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_102)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_625])).

tff(c_728,plain,(
    ! [A_112] :
      ( ~ v2_tex_2('#skF_3',A_112)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_112)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_577,c_629])).

tff(c_737,plain,
    ( ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_728])).

tff(c_743,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_544,c_473,c_737])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_743])).

tff(c_746,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_764,plain,(
    ! [A_113,B_114] :
      ( u1_struct_0('#skF_1'(A_113,B_114)) = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | v1_xboole_0(B_114)
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_767,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_764])).

tff(c_770,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_767])).

tff(c_771,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_770])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_789,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_10])).

tff(c_806,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_789])).

tff(c_807,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_806])).

tff(c_811,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_807])).

tff(c_815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.63  
% 3.14/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.63  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.54/1.63  
% 3.54/1.63  %Foreground sorts:
% 3.54/1.63  
% 3.54/1.63  
% 3.54/1.63  %Background operators:
% 3.54/1.63  
% 3.54/1.63  
% 3.54/1.63  %Foreground operators:
% 3.54/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.54/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.63  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.54/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.63  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.54/1.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.54/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.54/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.54/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.63  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.54/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.54/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.54/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.63  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.54/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.63  
% 3.54/1.67  tff(f_184, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.54/1.67  tff(f_144, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 3.54/1.67  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.54/1.67  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.54/1.67  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.54/1.67  tff(f_53, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 3.54/1.67  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A)) => (((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tex_1)).
% 3.54/1.67  tff(f_164, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 3.54/1.67  tff(f_123, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 3.54/1.67  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & ~v7_struct_0(B)) & v2_tdlat_3(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc23_tex_2)).
% 3.54/1.67  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.54/1.67  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_538, plain, (![A_97, B_98]: (m1_pre_topc('#skF_1'(A_97, B_98), A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | v1_xboole_0(B_98) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_540, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_538])).
% 3.54/1.67  tff(c_543, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_540])).
% 3.54/1.67  tff(c_544, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_543])).
% 3.54/1.67  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.54/1.67  tff(c_556, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_544, c_6])).
% 3.54/1.67  tff(c_570, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_556])).
% 3.54/1.67  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.67  tff(c_60, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_62, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 3.54/1.67  tff(c_54, plain, (~v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_65, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54])).
% 3.54/1.67  tff(c_274, plain, (![A_61, B_62]: (m1_pre_topc('#skF_1'(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | v1_xboole_0(B_62) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_278, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_274])).
% 3.54/1.67  tff(c_284, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_278])).
% 3.54/1.67  tff(c_285, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_284])).
% 3.54/1.67  tff(c_118, plain, (![A_51, B_52]: (~v2_struct_0('#skF_1'(A_51, B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | v1_xboole_0(B_52) | ~l1_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_121, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_118])).
% 3.54/1.67  tff(c_124, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_121])).
% 3.54/1.67  tff(c_125, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_124])).
% 3.54/1.67  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.54/1.67  tff(c_294, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_285, c_2])).
% 3.54/1.67  tff(c_308, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_294])).
% 3.54/1.67  tff(c_126, plain, (![A_53, B_54]: (u1_struct_0('#skF_1'(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | v1_xboole_0(B_54) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_129, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_126])).
% 3.54/1.67  tff(c_132, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_129])).
% 3.54/1.67  tff(c_133, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_132])).
% 3.54/1.67  tff(c_36, plain, (![A_19, B_23]: (~v2_struct_0('#skF_1'(A_19, B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | v1_xboole_0(B_23) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_140, plain, (![B_23]: (~v2_struct_0('#skF_1'('#skF_1'('#skF_2', '#skF_3'), B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1('#skF_3')) | v1_xboole_0(B_23) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_133, c_36])).
% 3.54/1.67  tff(c_153, plain, (![B_23]: (~v2_struct_0('#skF_1'('#skF_1'('#skF_2', '#skF_3'), B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1('#skF_3')) | v1_xboole_0(B_23) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_125, c_140])).
% 3.54/1.67  tff(c_164, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_153])).
% 3.54/1.67  tff(c_165, plain, (![A_55, B_56]: (m1_pre_topc('#skF_1'(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | v1_xboole_0(B_56) | ~l1_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_169, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_165])).
% 3.54/1.67  tff(c_173, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_169])).
% 3.54/1.67  tff(c_174, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_173])).
% 3.54/1.67  tff(c_186, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_174, c_6])).
% 3.54/1.67  tff(c_200, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_186])).
% 3.54/1.67  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_200])).
% 3.54/1.67  tff(c_204, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_153])).
% 3.54/1.67  tff(c_8, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.67  tff(c_146, plain, (~v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_8])).
% 3.54/1.67  tff(c_156, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_146])).
% 3.54/1.67  tff(c_159, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_156])).
% 3.54/1.67  tff(c_163, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_159])).
% 3.54/1.67  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_163])).
% 3.54/1.67  tff(c_219, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_156])).
% 3.54/1.67  tff(c_16, plain, (![A_11]: (v1_tdlat_3(A_11) | ~v2_pre_topc(A_11) | ~v7_struct_0(A_11) | v2_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.54/1.67  tff(c_223, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_219, c_16])).
% 3.54/1.67  tff(c_229, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_125, c_223])).
% 3.54/1.67  tff(c_233, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_229])).
% 3.54/1.67  tff(c_234, plain, (![A_59, B_60]: (m1_pre_topc('#skF_1'(A_59, B_60), A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | v1_xboole_0(B_60) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_238, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_234])).
% 3.54/1.67  tff(c_242, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_238])).
% 3.54/1.67  tff(c_243, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_242])).
% 3.54/1.67  tff(c_255, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_243, c_6])).
% 3.54/1.67  tff(c_269, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_255])).
% 3.54/1.67  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_269])).
% 3.54/1.67  tff(c_272, plain, (~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_229])).
% 3.54/1.67  tff(c_322, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_272])).
% 3.54/1.67  tff(c_436, plain, (![B_75, A_76]: (v2_tex_2(u1_struct_0(B_75), A_76) | ~v1_tdlat_3(B_75) | ~m1_subset_1(u1_struct_0(B_75), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_75, A_76) | v2_struct_0(B_75) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.54/1.67  tff(c_445, plain, (![A_76]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_76) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_76) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(superposition, [status(thm), theory('equality')], [c_133, c_436])).
% 3.54/1.67  tff(c_450, plain, (![A_76]: (v2_tex_2('#skF_3', A_76) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_76) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_133, c_445])).
% 3.54/1.67  tff(c_455, plain, (![A_77]: (v2_tex_2('#skF_3', A_77) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_77) | ~l1_pre_topc(A_77) | v2_struct_0(A_77))), inference(negUnitSimplification, [status(thm)], [c_125, c_450])).
% 3.54/1.67  tff(c_464, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_455])).
% 3.54/1.67  tff(c_470, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_285, c_464])).
% 3.54/1.67  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_65, c_470])).
% 3.54/1.67  tff(c_474, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 3.54/1.67  tff(c_473, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 3.54/1.67  tff(c_530, plain, (![A_95, B_96]: (~v2_struct_0('#skF_1'(A_95, B_96)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(B_96) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_533, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_530])).
% 3.54/1.67  tff(c_536, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_533])).
% 3.54/1.67  tff(c_537, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_536])).
% 3.54/1.67  tff(c_48, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.54/1.67  tff(c_28, plain, (![B_18, A_16]: (v2_tdlat_3(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16) | ~v2_tdlat_3(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.54/1.67  tff(c_550, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_544, c_28])).
% 3.54/1.67  tff(c_563, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_550])).
% 3.54/1.67  tff(c_564, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_563])).
% 3.54/1.67  tff(c_22, plain, (![B_14, A_12]: (~v1_tdlat_3(B_14) | ~v2_tdlat_3(B_14) | v7_struct_0(B_14) | v2_struct_0(B_14) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.54/1.67  tff(c_547, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_544, c_22])).
% 3.54/1.67  tff(c_559, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_547])).
% 3.54/1.67  tff(c_560, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_537, c_559])).
% 3.54/1.67  tff(c_576, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_564, c_560])).
% 3.54/1.67  tff(c_577, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_576])).
% 3.54/1.67  tff(c_580, plain, (![A_99, B_100]: (u1_struct_0('#skF_1'(A_99, B_100))=B_100 | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | v1_xboole_0(B_100) | ~l1_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_583, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_580])).
% 3.54/1.67  tff(c_586, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_583])).
% 3.54/1.67  tff(c_587, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_586])).
% 3.54/1.67  tff(c_622, plain, (![B_101, A_102]: (v1_tdlat_3(B_101) | ~v2_tex_2(u1_struct_0(B_101), A_102) | ~m1_subset_1(u1_struct_0(B_101), k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc(B_101, A_102) | v2_struct_0(B_101) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.54/1.67  tff(c_625, plain, (![A_102]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_102) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_102) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(superposition, [status(thm), theory('equality')], [c_587, c_622])).
% 3.54/1.67  tff(c_629, plain, (![A_102]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', A_102) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_102) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_587, c_625])).
% 3.54/1.67  tff(c_728, plain, (![A_112]: (~v2_tex_2('#skF_3', A_112) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_112) | ~l1_pre_topc(A_112) | v2_struct_0(A_112))), inference(negUnitSimplification, [status(thm)], [c_537, c_577, c_629])).
% 3.54/1.67  tff(c_737, plain, (~v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_728])).
% 3.54/1.67  tff(c_743, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_544, c_473, c_737])).
% 3.54/1.67  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_743])).
% 3.54/1.67  tff(c_746, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_576])).
% 3.54/1.67  tff(c_764, plain, (![A_113, B_114]: (u1_struct_0('#skF_1'(A_113, B_114))=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | v1_xboole_0(B_114) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.54/1.67  tff(c_767, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_764])).
% 3.54/1.67  tff(c_770, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_767])).
% 3.54/1.67  tff(c_771, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_770])).
% 3.54/1.67  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.67  tff(c_789, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_771, c_10])).
% 3.54/1.67  tff(c_806, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_746, c_789])).
% 3.54/1.67  tff(c_807, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_474, c_806])).
% 3.54/1.67  tff(c_811, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_807])).
% 3.54/1.67  tff(c_815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_570, c_811])).
% 3.54/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.67  
% 3.54/1.67  Inference rules
% 3.54/1.67  ----------------------
% 3.54/1.67  #Ref     : 0
% 3.54/1.67  #Sup     : 134
% 3.54/1.67  #Fact    : 0
% 3.54/1.67  #Define  : 0
% 3.54/1.67  #Split   : 6
% 3.54/1.67  #Chain   : 0
% 3.54/1.67  #Close   : 0
% 3.54/1.67  
% 3.54/1.67  Ordering : KBO
% 3.54/1.67  
% 3.54/1.67  Simplification rules
% 3.54/1.67  ----------------------
% 3.54/1.67  #Subsume      : 11
% 3.54/1.67  #Demod        : 120
% 3.54/1.67  #Tautology    : 42
% 3.54/1.67  #SimpNegUnit  : 61
% 3.54/1.67  #BackRed      : 0
% 3.54/1.67  
% 3.54/1.67  #Partial instantiations: 0
% 3.54/1.67  #Strategies tried      : 1
% 3.54/1.67  
% 3.54/1.67  Timing (in seconds)
% 3.54/1.67  ----------------------
% 3.54/1.67  Preprocessing        : 0.35
% 3.54/1.67  Parsing              : 0.19
% 3.54/1.67  CNF conversion       : 0.03
% 3.54/1.67  Main loop            : 0.43
% 3.54/1.67  Inferencing          : 0.16
% 3.54/1.67  Reduction            : 0.13
% 3.54/1.67  Demodulation         : 0.08
% 3.54/1.67  BG Simplification    : 0.02
% 3.54/1.67  Subsumption          : 0.09
% 3.54/1.67  Abstraction          : 0.02
% 3.54/1.67  MUC search           : 0.00
% 3.54/1.67  Cooper               : 0.00
% 3.54/1.67  Total                : 0.85
% 3.54/1.67  Index Insertion      : 0.00
% 3.54/1.67  Index Deletion       : 0.00
% 3.54/1.67  Index Matching       : 0.00
% 3.54/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
