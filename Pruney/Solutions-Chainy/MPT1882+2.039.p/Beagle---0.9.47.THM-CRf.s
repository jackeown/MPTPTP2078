%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:18 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 300 expanded)
%              Number of leaves         :   30 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 (1103 expanded)
%              Number of equality atoms :   15 (  69 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_72,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_185,plain,(
    ! [A_74,B_75] :
      ( '#skF_2'(A_74,B_75) != B_75
      | v3_tex_2(B_75,A_74)
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_188,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_185])).

tff(c_195,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_188])).

tff(c_196,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_195])).

tff(c_198,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_73,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58])).

tff(c_245,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ v1_zfmisc_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | v1_xboole_0(B_83)
      | ~ l1_pre_topc(A_84)
      | ~ v2_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_248,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_245])).

tff(c_255,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_73,c_248])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_198,c_255])).

tff(c_258,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_259,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_276,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,'#skF_2'(A_89,B_88))
      | v3_tex_2(B_88,A_89)
      | ~ v2_tex_2(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_278,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_276])).

tff(c_284,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_259,c_278])).

tff(c_285,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_284])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_89,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_96,plain,(
    ! [A_45,A_46] :
      ( ~ v1_xboole_0(A_45)
      | ~ r2_hidden(A_46,A_45) ) ),
    inference(resolution,[status(thm)],[c_59,c_89])).

tff(c_101,plain,(
    ! [A_47,B_48] :
      ( ~ v1_xboole_0(A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [B_48,A_47] :
      ( B_48 = A_47
      | ~ r1_tarski(B_48,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_296,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_285,c_104])).

tff(c_306,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_296])).

tff(c_32,plain,(
    ! [B_25,A_23] :
      ( B_25 = A_23
      | ~ r1_tarski(A_23,B_25)
      | ~ v1_zfmisc_1(B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_293,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_285,c_32])).

tff(c_303,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_258,c_293])).

tff(c_314,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_303])).

tff(c_265,plain,(
    ! [A_86,B_87] :
      ( v2_tex_2('#skF_2'(A_86,B_87),A_86)
      | v3_tex_2(B_87,A_86)
      | ~ v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_267,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_265])).

tff(c_273,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_259,c_267])).

tff(c_274,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_273])).

tff(c_494,plain,(
    ! [A_117,B_118] :
      ( m1_subset_1('#skF_2'(A_117,B_118),k1_zfmisc_1(u1_struct_0(A_117)))
      | v3_tex_2(B_118,A_117)
      | ~ v2_tex_2(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [B_31,A_29] :
      ( v1_zfmisc_1(B_31)
      | ~ v2_tex_2(B_31,A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_29)
      | ~ v2_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_930,plain,(
    ! [A_181,B_182] :
      ( v1_zfmisc_1('#skF_2'(A_181,B_182))
      | ~ v2_tex_2('#skF_2'(A_181,B_182),A_181)
      | v1_xboole_0('#skF_2'(A_181,B_182))
      | ~ v2_tdlat_3(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181)
      | v3_tex_2(B_182,A_181)
      | ~ v2_tex_2(B_182,A_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(resolution,[status(thm)],[c_494,c_38])).

tff(c_936,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_274,c_930])).

tff(c_943,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_259,c_48,c_46,c_936])).

tff(c_945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_50,c_306,c_314,c_943])).

tff(c_946,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_947,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1027,plain,(
    ! [B_211,A_212] :
      ( v2_tex_2(B_211,A_212)
      | ~ v3_tex_2(B_211,A_212)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1030,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1027])).

tff(c_1037,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_947,c_1030])).

tff(c_1132,plain,(
    ! [B_235,A_236] :
      ( v1_zfmisc_1(B_235)
      | ~ v2_tex_2(B_235,A_236)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_236)))
      | v1_xboole_0(B_235)
      | ~ l1_pre_topc(A_236)
      | ~ v2_tdlat_3(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1135,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1132])).

tff(c_1142,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1037,c_1135])).

tff(c_1144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_946,c_1142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 12:55:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.60  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.48/1.60  
% 3.48/1.60  %Foreground sorts:
% 3.48/1.60  
% 3.48/1.60  
% 3.48/1.60  %Background operators:
% 3.48/1.60  
% 3.48/1.60  
% 3.48/1.60  %Foreground operators:
% 3.48/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.48/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.60  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.48/1.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.48/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.48/1.60  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.48/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.48/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.48/1.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.48/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.48/1.60  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.48/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.60  
% 3.48/1.62  tff(f_133, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 3.48/1.62  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.48/1.62  tff(f_113, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 3.48/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.48/1.62  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.48/1.62  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.48/1.62  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.48/1.62  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.62  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.48/1.62  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_52, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_72, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.48/1.62  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_185, plain, (![A_74, B_75]: ('#skF_2'(A_74, B_75)!=B_75 | v3_tex_2(B_75, A_74) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.48/1.62  tff(c_188, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_185])).
% 3.48/1.62  tff(c_195, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_188])).
% 3.48/1.62  tff(c_196, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_195])).
% 3.48/1.62  tff(c_198, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_196])).
% 3.48/1.62  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_46, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_58, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.48/1.62  tff(c_73, plain, (v1_zfmisc_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_58])).
% 3.48/1.62  tff(c_245, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~v1_zfmisc_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | v1_xboole_0(B_83) | ~l1_pre_topc(A_84) | ~v2_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.48/1.62  tff(c_248, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_245])).
% 3.48/1.62  tff(c_255, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_73, c_248])).
% 3.48/1.62  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_198, c_255])).
% 3.48/1.62  tff(c_258, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_196])).
% 3.48/1.62  tff(c_259, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_196])).
% 3.48/1.62  tff(c_276, plain, (![B_88, A_89]: (r1_tarski(B_88, '#skF_2'(A_89, B_88)) | v3_tex_2(B_88, A_89) | ~v2_tex_2(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.48/1.62  tff(c_278, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_276])).
% 3.48/1.62  tff(c_284, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_259, c_278])).
% 3.48/1.62  tff(c_285, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_284])).
% 3.48/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.48/1.62  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.62  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.48/1.62  tff(c_59, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.48/1.62  tff(c_89, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.48/1.62  tff(c_96, plain, (![A_45, A_46]: (~v1_xboole_0(A_45) | ~r2_hidden(A_46, A_45))), inference(resolution, [status(thm)], [c_59, c_89])).
% 3.48/1.62  tff(c_101, plain, (![A_47, B_48]: (~v1_xboole_0(A_47) | r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_6, c_96])).
% 3.48/1.62  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.48/1.62  tff(c_104, plain, (![B_48, A_47]: (B_48=A_47 | ~r1_tarski(B_48, A_47) | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_101, c_8])).
% 3.48/1.62  tff(c_296, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_285, c_104])).
% 3.48/1.62  tff(c_306, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_258, c_296])).
% 3.48/1.62  tff(c_32, plain, (![B_25, A_23]: (B_25=A_23 | ~r1_tarski(A_23, B_25) | ~v1_zfmisc_1(B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.62  tff(c_293, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_285, c_32])).
% 3.48/1.62  tff(c_303, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_258, c_293])).
% 3.48/1.62  tff(c_314, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_306, c_303])).
% 3.48/1.62  tff(c_265, plain, (![A_86, B_87]: (v2_tex_2('#skF_2'(A_86, B_87), A_86) | v3_tex_2(B_87, A_86) | ~v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.48/1.62  tff(c_267, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_265])).
% 3.48/1.62  tff(c_273, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_259, c_267])).
% 3.48/1.62  tff(c_274, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_273])).
% 3.48/1.62  tff(c_494, plain, (![A_117, B_118]: (m1_subset_1('#skF_2'(A_117, B_118), k1_zfmisc_1(u1_struct_0(A_117))) | v3_tex_2(B_118, A_117) | ~v2_tex_2(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.48/1.62  tff(c_38, plain, (![B_31, A_29]: (v1_zfmisc_1(B_31) | ~v2_tex_2(B_31, A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | v1_xboole_0(B_31) | ~l1_pre_topc(A_29) | ~v2_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.48/1.62  tff(c_930, plain, (![A_181, B_182]: (v1_zfmisc_1('#skF_2'(A_181, B_182)) | ~v2_tex_2('#skF_2'(A_181, B_182), A_181) | v1_xboole_0('#skF_2'(A_181, B_182)) | ~v2_tdlat_3(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181) | v3_tex_2(B_182, A_181) | ~v2_tex_2(B_182, A_181) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(resolution, [status(thm)], [c_494, c_38])).
% 3.48/1.62  tff(c_936, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_274, c_930])).
% 3.48/1.62  tff(c_943, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_259, c_48, c_46, c_936])).
% 3.48/1.62  tff(c_945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_50, c_306, c_314, c_943])).
% 3.48/1.62  tff(c_946, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.48/1.62  tff(c_947, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.48/1.62  tff(c_1027, plain, (![B_211, A_212]: (v2_tex_2(B_211, A_212) | ~v3_tex_2(B_211, A_212) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.48/1.62  tff(c_1030, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1027])).
% 3.48/1.62  tff(c_1037, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_947, c_1030])).
% 3.48/1.62  tff(c_1132, plain, (![B_235, A_236]: (v1_zfmisc_1(B_235) | ~v2_tex_2(B_235, A_236) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_236))) | v1_xboole_0(B_235) | ~l1_pre_topc(A_236) | ~v2_tdlat_3(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.48/1.62  tff(c_1135, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1132])).
% 3.48/1.62  tff(c_1142, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1037, c_1135])).
% 3.48/1.62  tff(c_1144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_946, c_1142])).
% 3.48/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.62  
% 3.48/1.62  Inference rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Ref     : 0
% 3.48/1.62  #Sup     : 229
% 3.48/1.62  #Fact    : 0
% 3.48/1.62  #Define  : 0
% 3.48/1.62  #Split   : 7
% 3.48/1.62  #Chain   : 0
% 3.48/1.62  #Close   : 0
% 3.48/1.62  
% 3.48/1.62  Ordering : KBO
% 3.48/1.62  
% 3.48/1.62  Simplification rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Subsume      : 80
% 3.48/1.62  #Demod        : 80
% 3.48/1.62  #Tautology    : 41
% 3.48/1.62  #SimpNegUnit  : 26
% 3.48/1.62  #BackRed      : 0
% 3.48/1.62  
% 3.48/1.62  #Partial instantiations: 0
% 3.48/1.62  #Strategies tried      : 1
% 3.48/1.62  
% 3.48/1.62  Timing (in seconds)
% 3.48/1.62  ----------------------
% 3.48/1.62  Preprocessing        : 0.29
% 3.48/1.62  Parsing              : 0.16
% 3.48/1.62  CNF conversion       : 0.02
% 3.48/1.62  Main loop            : 0.49
% 3.48/1.62  Inferencing          : 0.18
% 3.48/1.62  Reduction            : 0.13
% 3.48/1.62  Demodulation         : 0.08
% 3.48/1.62  BG Simplification    : 0.02
% 3.48/1.62  Subsumption          : 0.13
% 3.48/1.62  Abstraction          : 0.02
% 3.48/1.62  MUC search           : 0.00
% 3.48/1.62  Cooper               : 0.00
% 3.48/1.62  Total                : 0.82
% 3.48/1.62  Index Insertion      : 0.00
% 3.48/1.62  Index Deletion       : 0.00
% 3.48/1.62  Index Matching       : 0.00
% 3.48/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
