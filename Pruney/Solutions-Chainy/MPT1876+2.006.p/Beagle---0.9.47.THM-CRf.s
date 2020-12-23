%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:51 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 492 expanded)
%              Number of leaves         :   32 ( 190 expanded)
%              Depth                    :   14
%              Number of atoms          :  323 (2003 expanded)
%              Number of equality atoms :   10 (  50 expanded)
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

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & v2_pre_topc(B) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & v2_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

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

tff(f_81,axiom,(
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

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_313,plain,(
    ! [A_83,B_84] :
      ( m1_pre_topc('#skF_1'(A_83,B_84),A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | v1_xboole_0(B_84)
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_315,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_313])).

tff(c_318,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_315])).

tff(c_319,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_318])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_337,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_319,c_6])).

tff(c_359,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_337])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_58,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_60,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50])).

tff(c_129,plain,(
    ! [A_56,B_57] :
      ( m1_pre_topc('#skF_1'(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | v1_xboole_0(B_57)
      | ~ l1_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_133,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_137,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_133])).

tff(c_138,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_137])).

tff(c_80,plain,(
    ! [A_50,B_51] :
      ( ~ v2_struct_0('#skF_1'(A_50,B_51))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_83,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_86,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_87,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_86])).

tff(c_156,plain,
    ( l1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_6])).

tff(c_178,plain,(
    l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_156])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_153,plain,
    ( v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_175,plain,(
    v2_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_153])).

tff(c_18,plain,(
    ! [B_15,A_13] :
      ( v1_tdlat_3(B_15)
      | ~ v2_pre_topc(B_15)
      | ~ v7_struct_0(B_15)
      | v2_struct_0(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_144,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_18])).

tff(c_163,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_144])).

tff(c_164,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_87,c_163])).

tff(c_184,plain,
    ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_164])).

tff(c_185,plain,(
    ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_96,plain,(
    ! [A_54,B_55] :
      ( u1_struct_0('#skF_1'(A_54,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(B_55)
      | ~ l1_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_99,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_102,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_99])).

tff(c_103,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_102])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_116,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_8])).

tff(c_126,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_116])).

tff(c_186,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_126])).

tff(c_189,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_189])).

tff(c_194,plain,(
    v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_196,plain,(
    ! [B_58,A_59] :
      ( v2_tex_2(u1_struct_0(B_58),A_59)
      | ~ v1_tdlat_3(B_58)
      | ~ m1_subset_1(u1_struct_0(B_58),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_pre_topc(B_58,A_59)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_199,plain,(
    ! [A_59] :
      ( v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_59)
      | ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_59)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_196])).

tff(c_204,plain,(
    ! [A_59] :
      ( v2_tex_2('#skF_3',A_59)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_59)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_103,c_199])).

tff(c_256,plain,(
    ! [A_63] :
      ( v2_tex_2('#skF_3',A_63)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_63)
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_204])).

tff(c_265,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_256])).

tff(c_271,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_138,c_265])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_60,c_271])).

tff(c_274,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_305,plain,(
    ! [A_81,B_82] :
      ( ~ v2_struct_0('#skF_1'(A_81,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_xboole_0(B_82)
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_308,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_305])).

tff(c_311,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_308])).

tff(c_312,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_311])).

tff(c_44,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_24,plain,(
    ! [B_19,A_17] :
      ( v2_tdlat_3(B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_tdlat_3(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_331,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_319,c_24])).

tff(c_352,plain,
    ( v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_331])).

tff(c_353,plain,(
    v2_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_352])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( ~ v1_tdlat_3(B_12)
      | ~ v2_tdlat_3(B_12)
      | v7_struct_0(B_12)
      | v2_struct_0(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_325,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_319,c_12])).

tff(c_344,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_325])).

tff(c_345,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_312,c_344])).

tff(c_407,plain,
    ( ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
    | v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_345])).

tff(c_408,plain,(
    ~ v1_tdlat_3('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_364,plain,(
    ! [A_85,B_86] :
      ( u1_struct_0('#skF_1'(A_85,B_86)) = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_xboole_0(B_86)
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_367,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_364])).

tff(c_370,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_367])).

tff(c_371,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_370])).

tff(c_511,plain,(
    ! [B_96,A_97] :
      ( v1_tdlat_3(B_96)
      | ~ v2_tex_2(u1_struct_0(B_96),A_97)
      | ~ m1_subset_1(u1_struct_0(B_96),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc(B_96,A_97)
      | v2_struct_0(B_96)
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_520,plain,(
    ! [A_97] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_97)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_97)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_511])).

tff(c_524,plain,(
    ! [A_97] :
      ( v1_tdlat_3('#skF_1'('#skF_2','#skF_3'))
      | ~ v2_tex_2('#skF_3',A_97)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_97)
      | v2_struct_0('#skF_1'('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_520])).

tff(c_529,plain,(
    ! [A_98] :
      ( ~ v2_tex_2('#skF_3',A_98)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_98)
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_408,c_524])).

tff(c_538,plain,
    ( ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_529])).

tff(c_544,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_319,c_274,c_538])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_544])).

tff(c_547,plain,(
    v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_275,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_386,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_10])).

tff(c_404,plain,
    ( ~ l1_struct_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_386])).

tff(c_552,plain,(
    ~ l1_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_404])).

tff(c_555,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_552])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.37  
% 2.85/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.37  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.85/1.37  
% 2.85/1.37  %Foreground sorts:
% 2.85/1.37  
% 2.85/1.37  
% 2.85/1.37  %Background operators:
% 2.85/1.37  
% 2.85/1.37  
% 2.85/1.37  %Foreground operators:
% 2.85/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.85/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.37  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.85/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.85/1.37  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.85/1.37  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.85/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.37  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.85/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.85/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.37  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.85/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.85/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.85/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.37  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.85/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.37  
% 2.85/1.40  tff(f_184, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.85/1.40  tff(f_144, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 2.85/1.40  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.85/1.40  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.85/1.40  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.85/1.40  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & v7_struct_0(B)) & v2_pre_topc(B)) => ((~v2_struct_0(B) & v1_tdlat_3(B)) & v2_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc25_tex_2)).
% 2.85/1.40  tff(f_53, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.85/1.40  tff(f_164, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.85/1.40  tff(f_123, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 2.85/1.40  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & ~v7_struct_0(B)) & v2_tdlat_3(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc23_tex_2)).
% 2.85/1.40  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.85/1.40  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_313, plain, (![A_83, B_84]: (m1_pre_topc('#skF_1'(A_83, B_84), A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | v1_xboole_0(B_84) | ~l1_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.85/1.40  tff(c_315, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_313])).
% 2.85/1.40  tff(c_318, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_315])).
% 2.85/1.40  tff(c_319, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_318])).
% 2.85/1.40  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.85/1.40  tff(c_337, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_319, c_6])).
% 2.85/1.40  tff(c_359, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_337])).
% 2.85/1.40  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.40  tff(c_56, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_58, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 2.85/1.40  tff(c_50, plain, (~v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_60, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50])).
% 2.85/1.40  tff(c_129, plain, (![A_56, B_57]: (m1_pre_topc('#skF_1'(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | v1_xboole_0(B_57) | ~l1_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.85/1.40  tff(c_133, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_129])).
% 2.85/1.40  tff(c_137, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_133])).
% 2.85/1.40  tff(c_138, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_137])).
% 2.85/1.40  tff(c_80, plain, (![A_50, B_51]: (~v2_struct_0('#skF_1'(A_50, B_51)) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.85/1.40  tff(c_83, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_80])).
% 2.85/1.40  tff(c_86, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_83])).
% 2.85/1.40  tff(c_87, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_86])).
% 2.85/1.40  tff(c_156, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_138, c_6])).
% 2.85/1.40  tff(c_178, plain, (l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_156])).
% 2.85/1.40  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.85/1.40  tff(c_153, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_138, c_2])).
% 2.85/1.40  tff(c_175, plain, (v2_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_153])).
% 2.85/1.40  tff(c_18, plain, (![B_15, A_13]: (v1_tdlat_3(B_15) | ~v2_pre_topc(B_15) | ~v7_struct_0(B_15) | v2_struct_0(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.85/1.40  tff(c_144, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_138, c_18])).
% 2.85/1.40  tff(c_163, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_144])).
% 2.85/1.40  tff(c_164, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_87, c_163])).
% 2.85/1.40  tff(c_184, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_164])).
% 2.85/1.40  tff(c_185, plain, (~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_184])).
% 2.85/1.40  tff(c_96, plain, (![A_54, B_55]: (u1_struct_0('#skF_1'(A_54, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(B_55) | ~l1_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.85/1.40  tff(c_99, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_96])).
% 2.85/1.40  tff(c_102, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_99])).
% 2.85/1.40  tff(c_103, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_102])).
% 2.85/1.40  tff(c_8, plain, (![A_8]: (~v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.85/1.40  tff(c_116, plain, (~v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_8])).
% 2.85/1.40  tff(c_126, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_116])).
% 2.85/1.40  tff(c_186, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_185, c_126])).
% 2.85/1.40  tff(c_189, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_186])).
% 2.85/1.40  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_189])).
% 2.85/1.40  tff(c_194, plain, (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_184])).
% 2.85/1.40  tff(c_196, plain, (![B_58, A_59]: (v2_tex_2(u1_struct_0(B_58), A_59) | ~v1_tdlat_3(B_58) | ~m1_subset_1(u1_struct_0(B_58), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_pre_topc(B_58, A_59) | v2_struct_0(B_58) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.85/1.40  tff(c_199, plain, (![A_59]: (v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_59) | ~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_59) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(superposition, [status(thm), theory('equality')], [c_103, c_196])).
% 2.85/1.40  tff(c_204, plain, (![A_59]: (v2_tex_2('#skF_3', A_59) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_59) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_103, c_199])).
% 2.85/1.40  tff(c_256, plain, (![A_63]: (v2_tex_2('#skF_3', A_63) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_63) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(negUnitSimplification, [status(thm)], [c_87, c_204])).
% 2.85/1.40  tff(c_265, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_256])).
% 2.85/1.40  tff(c_271, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_138, c_265])).
% 2.85/1.40  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_60, c_271])).
% 2.85/1.40  tff(c_274, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.85/1.40  tff(c_305, plain, (![A_81, B_82]: (~v2_struct_0('#skF_1'(A_81, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | v1_xboole_0(B_82) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.85/1.40  tff(c_308, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_305])).
% 2.85/1.40  tff(c_311, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_308])).
% 2.85/1.40  tff(c_312, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_311])).
% 2.85/1.40  tff(c_44, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.85/1.40  tff(c_24, plain, (![B_19, A_17]: (v2_tdlat_3(B_19) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17) | ~v2_tdlat_3(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.85/1.40  tff(c_331, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_319, c_24])).
% 2.85/1.40  tff(c_352, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_331])).
% 2.85/1.40  tff(c_353, plain, (v2_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_352])).
% 2.85/1.40  tff(c_12, plain, (![B_12, A_10]: (~v1_tdlat_3(B_12) | ~v2_tdlat_3(B_12) | v7_struct_0(B_12) | v2_struct_0(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.85/1.40  tff(c_325, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_319, c_12])).
% 2.85/1.40  tff(c_344, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_325])).
% 2.85/1.40  tff(c_345, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_312, c_344])).
% 2.85/1.40  tff(c_407, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_345])).
% 2.85/1.40  tff(c_408, plain, (~v1_tdlat_3('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_407])).
% 2.85/1.40  tff(c_364, plain, (![A_85, B_86]: (u1_struct_0('#skF_1'(A_85, B_86))=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | v1_xboole_0(B_86) | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.85/1.40  tff(c_367, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_364])).
% 2.85/1.40  tff(c_370, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_367])).
% 2.85/1.40  tff(c_371, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_370])).
% 2.85/1.40  tff(c_511, plain, (![B_96, A_97]: (v1_tdlat_3(B_96) | ~v2_tex_2(u1_struct_0(B_96), A_97) | ~m1_subset_1(u1_struct_0(B_96), k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_pre_topc(B_96, A_97) | v2_struct_0(B_96) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.85/1.40  tff(c_520, plain, (![A_97]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_97) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_97) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(superposition, [status(thm), theory('equality')], [c_371, c_511])).
% 2.85/1.40  tff(c_524, plain, (![A_97]: (v1_tdlat_3('#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', A_97) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_97) | v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_520])).
% 2.85/1.40  tff(c_529, plain, (![A_98]: (~v2_tex_2('#skF_3', A_98) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_98) | ~l1_pre_topc(A_98) | v2_struct_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_312, c_408, c_524])).
% 2.85/1.40  tff(c_538, plain, (~v2_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_529])).
% 2.85/1.40  tff(c_544, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_319, c_274, c_538])).
% 2.85/1.40  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_544])).
% 2.85/1.40  tff(c_547, plain, (v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_407])).
% 2.85/1.40  tff(c_275, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 2.85/1.40  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.40  tff(c_386, plain, (v1_zfmisc_1('#skF_3') | ~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_10])).
% 2.85/1.40  tff(c_404, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_275, c_386])).
% 2.85/1.40  tff(c_552, plain, (~l1_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_404])).
% 2.85/1.40  tff(c_555, plain, (~l1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_552])).
% 2.85/1.40  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_359, c_555])).
% 2.85/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.40  
% 2.85/1.40  Inference rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Ref     : 0
% 2.85/1.40  #Sup     : 85
% 2.85/1.40  #Fact    : 0
% 2.85/1.40  #Define  : 0
% 2.85/1.40  #Split   : 4
% 2.85/1.40  #Chain   : 0
% 2.85/1.40  #Close   : 0
% 2.85/1.40  
% 2.85/1.40  Ordering : KBO
% 2.85/1.40  
% 2.85/1.40  Simplification rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Subsume      : 6
% 2.85/1.40  #Demod        : 86
% 2.85/1.40  #Tautology    : 23
% 2.85/1.40  #SimpNegUnit  : 41
% 2.85/1.40  #BackRed      : 0
% 2.85/1.40  
% 2.85/1.40  #Partial instantiations: 0
% 2.85/1.40  #Strategies tried      : 1
% 2.85/1.40  
% 2.85/1.40  Timing (in seconds)
% 2.85/1.40  ----------------------
% 2.85/1.40  Preprocessing        : 0.31
% 2.85/1.40  Parsing              : 0.17
% 2.85/1.40  CNF conversion       : 0.02
% 2.85/1.40  Main loop            : 0.31
% 2.85/1.40  Inferencing          : 0.11
% 2.85/1.40  Reduction            : 0.09
% 2.85/1.40  Demodulation         : 0.06
% 2.85/1.40  BG Simplification    : 0.02
% 2.85/1.40  Subsumption          : 0.06
% 2.85/1.40  Abstraction          : 0.01
% 2.85/1.40  MUC search           : 0.00
% 2.85/1.40  Cooper               : 0.00
% 2.85/1.40  Total                : 0.66
% 2.85/1.40  Index Insertion      : 0.00
% 2.85/1.40  Index Deletion       : 0.00
% 2.85/1.40  Index Matching       : 0.00
% 2.85/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
