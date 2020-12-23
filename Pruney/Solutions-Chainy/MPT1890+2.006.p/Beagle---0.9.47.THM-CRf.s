%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:24 EST 2020

% Result     : Theorem 8.91s
% Output     : CNFRefutation 9.27s
% Verified   : 
% Statistics : Number of formulae       :  222 (2417 expanded)
%              Number of leaves         :   37 ( 817 expanded)
%              Depth                    :   26
%              Number of atoms          :  562 (8142 expanded)
%              Number of equality atoms :   38 ( 927 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_52,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2288,plain,(
    ! [A_286,B_287] :
      ( r2_hidden('#skF_3'(A_286,B_287),B_287)
      | v2_tex_2(B_287,A_286)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2303,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2288])).

tff(c_2311,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2303])).

tff(c_2312,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_2311])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | ~ r1_tarski(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [A_56] : r2_hidden(A_56,k1_tarski(A_56)) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_176,plain,(
    ! [C_79,B_80,A_81] :
      ( ~ v1_xboole_0(C_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(C_79))
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_188,plain,(
    ! [B_82,A_83,A_84] :
      ( ~ v1_xboole_0(B_82)
      | ~ r2_hidden(A_83,A_84)
      | ~ r1_tarski(A_84,B_82) ) ),
    inference(resolution,[status(thm)],[c_28,c_176])).

tff(c_198,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | ~ r1_tarski(k1_tarski(A_86),B_85) ) ),
    inference(resolution,[status(thm)],[c_102,c_188])).

tff(c_207,plain,(
    ! [A_86] : ~ v1_xboole_0(k1_tarski(A_86)) ),
    inference(resolution,[status(thm)],[c_12,c_198])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [B_69,A_70] :
      ( m1_subset_1(B_69,A_70)
      | ~ r2_hidden(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_159,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_412,plain,(
    ! [B_116,B_117,A_118] :
      ( r2_hidden(B_116,B_117)
      | ~ r1_tarski(A_118,B_117)
      | ~ m1_subset_1(B_116,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_420,plain,(
    ! [B_116,B_9,A_8] :
      ( r2_hidden(B_116,B_9)
      | ~ m1_subset_1(B_116,k1_tarski(A_8))
      | v1_xboole_0(k1_tarski(A_8))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_412])).

tff(c_2013,plain,(
    ! [B_255,B_256,A_257] :
      ( r2_hidden(B_255,B_256)
      | ~ m1_subset_1(B_255,k1_tarski(A_257))
      | ~ r2_hidden(A_257,B_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_420])).

tff(c_2016,plain,(
    ! [A_257,B_2,B_256] :
      ( r2_hidden('#skF_1'(k1_tarski(A_257),B_2),B_256)
      | ~ r2_hidden(A_257,B_256)
      | v1_xboole_0(k1_tarski(A_257))
      | r1_tarski(k1_tarski(A_257),B_2) ) ),
    inference(resolution,[status(thm)],[c_156,c_2013])).

tff(c_4084,plain,(
    ! [A_386,B_387,B_388] :
      ( r2_hidden('#skF_1'(k1_tarski(A_386),B_387),B_388)
      | ~ r2_hidden(A_386,B_388)
      | r1_tarski(k1_tarski(A_386),B_387) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_2016])).

tff(c_186,plain,(
    ! [A_81] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_81,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_176])).

tff(c_187,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_103,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_425,plain,(
    ! [B_116] :
      ( r2_hidden(B_116,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_116,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_116,c_412])).

tff(c_430,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_741,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_3'(A_151,B_152),B_152)
      | v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_756,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_741])).

tff(c_764,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_756])).

tff(c_765,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_764])).

tff(c_206,plain,(
    ! [B_9,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_198])).

tff(c_768,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_765,c_206])).

tff(c_779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_768])).

tff(c_781,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_2048,plain,(
    ! [A_261,B_262,B_263] :
      ( r2_hidden('#skF_1'(A_261,B_262),B_263)
      | ~ r1_tarski(A_261,B_263)
      | r1_tarski(A_261,B_262) ) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2817,plain,(
    ! [A_319,B_320,B_321] :
      ( m1_subset_1('#skF_1'(A_319,B_320),B_321)
      | v1_xboole_0(B_321)
      | ~ r1_tarski(A_319,B_321)
      | r1_tarski(A_319,B_320) ) ),
    inference(resolution,[status(thm)],[c_2048,c_18])).

tff(c_782,plain,(
    ! [B_153] :
      ( r2_hidden(B_153,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_153,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_803,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_782,c_4])).

tff(c_2838,plain,(
    ! [A_319] :
      ( v1_xboole_0('#skF_5')
      | ~ r1_tarski(A_319,'#skF_5')
      | r1_tarski(A_319,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2817,c_803])).

tff(c_2890,plain,(
    ! [A_324] :
      ( ~ r1_tarski(A_324,'#skF_5')
      | r1_tarski(A_324,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_781,c_2838])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | ~ r1_tarski(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2957,plain,(
    ! [A_325] :
      ( r2_hidden(A_325,u1_struct_0('#skF_4'))
      | ~ r1_tarski(k1_tarski(A_325),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2890,c_14])).

tff(c_2967,plain,(
    ! [A_325] :
      ( m1_subset_1(A_325,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(k1_tarski(A_325),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2957,c_18])).

tff(c_2979,plain,(
    ! [A_326] :
      ( m1_subset_1(A_326,u1_struct_0('#skF_4'))
      | ~ r1_tarski(k1_tarski(A_326),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2967])).

tff(c_2989,plain,(
    ! [A_327] :
      ( m1_subset_1(A_327,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_327,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_2979])).

tff(c_134,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_1'(A_67,B_68),B_68)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_67,A_10] :
      ( r1_tarski(A_67,A_10)
      | ~ m1_subset_1('#skF_1'(A_67,A_10),A_10)
      | v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_134])).

tff(c_2993,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_67,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2989,c_145])).

tff(c_3002,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_67,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2993])).

tff(c_4118,plain,(
    ! [A_386] :
      ( ~ r2_hidden(A_386,'#skF_5')
      | r1_tarski(k1_tarski(A_386),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4084,c_3002])).

tff(c_2153,plain,(
    ! [A_273,B_274] :
      ( v4_pre_topc(k2_pre_topc(A_273,B_274),A_273)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2172,plain,(
    ! [A_273,A_12] :
      ( v4_pre_topc(k2_pre_topc(A_273,A_12),A_273)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | ~ r1_tarski(A_12,u1_struct_0(A_273)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2153])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_pre_topc(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2322,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2312,c_18])).

tff(c_2328,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_781,c_2322])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2354,plain,(
    ! [B_289] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_289)
      | ~ r1_tarski('#skF_5',B_289) ) ),
    inference(resolution,[status(thm)],[c_2312,c_2])).

tff(c_2457,plain,(
    ! [B_295,B_296] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_295)
      | ~ r1_tarski(B_296,B_295)
      | ~ r1_tarski('#skF_5',B_296) ) ),
    inference(resolution,[status(thm)],[c_2354,c_2])).

tff(c_2463,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_2457])).

tff(c_2472,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2463])).

tff(c_2484,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2472,c_18])).

tff(c_2490,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2484])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k6_domain_1(A_19,B_20) = k1_tarski(B_20)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2493,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2490,c_34])).

tff(c_2499,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2493])).

tff(c_2414,plain,(
    ! [B_294] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5'),B_294)
      | v1_xboole_0(B_294)
      | ~ r1_tarski('#skF_5',B_294) ) ),
    inference(resolution,[status(thm)],[c_2354,c_18])).

tff(c_6993,plain,(
    ! [B_493] :
      ( k6_domain_1(B_493,'#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | v1_xboole_0(B_493)
      | ~ r1_tarski('#skF_5',B_493) ) ),
    inference(resolution,[status(thm)],[c_2414,c_34])).

tff(c_54,plain,(
    ! [C_45] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_45))) = k6_domain_1(u1_struct_0('#skF_4'),C_45)
      | ~ r2_hidden(C_45,'#skF_5')
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_7048,plain,
    ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5')))) = k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6993,c_54])).

tff(c_7137,plain,
    ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5')))) = k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_2490,c_2312,c_2499,c_7048])).

tff(c_7138,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5')))) = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_7137])).

tff(c_792,plain,(
    ! [B_153] :
      ( m1_subset_1(B_153,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_153,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_782,c_18])).

tff(c_804,plain,(
    ! [B_154] :
      ( m1_subset_1(B_154,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_154,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_792])).

tff(c_811,plain,(
    ! [B_154] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_154) = k1_tarski(B_154)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_154,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_804,c_34])).

tff(c_820,plain,(
    ! [B_154] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_154) = k1_tarski(B_154)
      | ~ m1_subset_1(B_154,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_811])).

tff(c_2580,plain,(
    ! [A_301,B_302,D_303] :
      ( k9_subset_1(u1_struct_0(A_301),B_302,D_303) != k6_domain_1(u1_struct_0(A_301),'#skF_3'(A_301,B_302))
      | ~ v3_pre_topc(D_303,A_301)
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0(A_301)))
      | v2_tex_2(B_302,A_301)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2587,plain,(
    ! [B_302,D_303] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_302,D_303) != k1_tarski('#skF_3'('#skF_4',B_302))
      | ~ v3_pre_topc(D_303,'#skF_4')
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_302,'#skF_4')
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',B_302),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_2580])).

tff(c_2597,plain,(
    ! [B_302,D_303] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_302,D_303) != k1_tarski('#skF_3'('#skF_4',B_302))
      | ~ v3_pre_topc(D_303,'#skF_4')
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_302,'#skF_4')
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',B_302),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2587])).

tff(c_2598,plain,(
    ! [B_302,D_303] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_302,D_303) != k1_tarski('#skF_3'('#skF_4',B_302))
      | ~ v3_pre_topc(D_303,'#skF_4')
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_302,'#skF_4')
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_3'('#skF_4',B_302),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2597])).

tff(c_7374,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7138,c_2598])).

tff(c_7404,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2328,c_56,c_7374])).

tff(c_7405,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7404])).

tff(c_7422,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_7405])).

tff(c_7431,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_7422])).

tff(c_7442,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7431])).

tff(c_7459,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_7442])).

tff(c_7463,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4118,c_7459])).

tff(c_7479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2312,c_7463])).

tff(c_7480,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7405])).

tff(c_60,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_7481,plain,(
    m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_7405])).

tff(c_38,plain,(
    ! [B_26,A_23] :
      ( v3_pre_topc(B_26,A_23)
      | ~ v4_pre_topc(B_26,A_23)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v3_tdlat_3(A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7516,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_7481,c_38])).

tff(c_7557,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_60,c_7516])).

tff(c_7558,plain,(
    ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_7480,c_7557])).

tff(c_7623,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2172,c_7558])).

tff(c_7628,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_7623])).

tff(c_7631,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4118,c_7628])).

tff(c_7647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2312,c_7631])).

tff(c_7649,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_7715,plain,(
    ! [B_521,A_522,A_523] :
      ( ~ v1_xboole_0(B_521)
      | ~ r2_hidden(A_522,A_523)
      | ~ r1_tarski(A_523,B_521) ) ),
    inference(resolution,[status(thm)],[c_28,c_176])).

tff(c_7726,plain,(
    ! [B_525,A_526] :
      ( ~ v1_xboole_0(B_525)
      | ~ r1_tarski(k1_tarski(A_526),B_525) ) ),
    inference(resolution,[status(thm)],[c_102,c_7715])).

tff(c_7749,plain,(
    ! [B_529,A_530] :
      ( ~ v1_xboole_0(B_529)
      | ~ r2_hidden(A_530,B_529) ) ),
    inference(resolution,[status(thm)],[c_16,c_7726])).

tff(c_7762,plain,(
    ! [A_531,B_532] :
      ( ~ v1_xboole_0(A_531)
      | r1_tarski(A_531,B_532) ) ),
    inference(resolution,[status(thm)],[c_6,c_7749])).

tff(c_120,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_127,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_120])).

tff(c_133,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_7773,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7762,c_133])).

tff(c_7785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7649,c_7773])).

tff(c_7786,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_7803,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7786,c_56])).

tff(c_16023,plain,(
    ! [A_1074,B_1075] :
      ( r2_hidden('#skF_3'(A_1074,B_1075),B_1075)
      | v2_tex_2(B_1075,A_1074)
      | ~ m1_subset_1(B_1075,k1_zfmisc_1(u1_struct_0(A_1074)))
      | ~ l1_pre_topc(A_1074)
      | ~ v2_pre_topc(A_1074)
      | v2_struct_0(A_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16032,plain,(
    ! [B_1075] :
      ( r2_hidden('#skF_3'('#skF_4',B_1075),B_1075)
      | v2_tex_2(B_1075,'#skF_4')
      | ~ m1_subset_1(B_1075,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7786,c_16023])).

tff(c_16043,plain,(
    ! [B_1075] :
      ( r2_hidden('#skF_3'('#skF_4',B_1075),B_1075)
      | v2_tex_2(B_1075,'#skF_4')
      | ~ m1_subset_1(B_1075,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_16032])).

tff(c_16080,plain,(
    ! [B_1082] :
      ( r2_hidden('#skF_3'('#skF_4',B_1082),B_1082)
      | v2_tex_2(B_1082,'#skF_4')
      | ~ m1_subset_1(B_1082,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_16043])).

tff(c_8506,plain,(
    ! [A_624,B_625] :
      ( r2_hidden('#skF_3'(A_624,B_625),B_625)
      | v2_tex_2(B_625,A_624)
      | ~ m1_subset_1(B_625,k1_zfmisc_1(u1_struct_0(A_624)))
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8528,plain,(
    ! [A_624,A_12] :
      ( r2_hidden('#skF_3'(A_624,A_12),A_12)
      | v2_tex_2(A_12,A_624)
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624)
      | ~ r1_tarski(A_12,u1_struct_0(A_624)) ) ),
    inference(resolution,[status(thm)],[c_28,c_8506])).

tff(c_7849,plain,(
    ! [C_545,B_546,A_547] :
      ( ~ v1_xboole_0(C_545)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(C_545))
      | ~ r2_hidden(A_547,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7857,plain,(
    ! [A_547] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_547,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7803,c_7849])).

tff(c_7860,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7857])).

tff(c_8515,plain,(
    ! [B_625] :
      ( r2_hidden('#skF_3'('#skF_4',B_625),B_625)
      | v2_tex_2(B_625,'#skF_4')
      | ~ m1_subset_1(B_625,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7786,c_8506])).

tff(c_8526,plain,(
    ! [B_625] :
      ( r2_hidden('#skF_3'('#skF_4',B_625),B_625)
      | v2_tex_2(B_625,'#skF_4')
      | ~ m1_subset_1(B_625,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_8515])).

tff(c_8530,plain,(
    ! [B_626] :
      ( r2_hidden('#skF_3'('#skF_4',B_626),B_626)
      | v2_tex_2(B_626,'#skF_4')
      | ~ m1_subset_1(B_626,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8526])).

tff(c_8558,plain,(
    ! [B_626] :
      ( m1_subset_1('#skF_3'('#skF_4',B_626),B_626)
      | v1_xboole_0(B_626)
      | v2_tex_2(B_626,'#skF_4')
      | ~ m1_subset_1(B_626,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8530,c_18])).

tff(c_8750,plain,(
    ! [A_642,B_643] :
      ( m1_subset_1('#skF_3'(A_642,B_643),u1_struct_0(A_642))
      | v2_tex_2(B_643,A_642)
      | ~ m1_subset_1(B_643,k1_zfmisc_1(u1_struct_0(A_642)))
      | ~ l1_pre_topc(A_642)
      | ~ v2_pre_topc(A_642)
      | v2_struct_0(A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8759,plain,(
    ! [B_643] :
      ( m1_subset_1('#skF_3'('#skF_4',B_643),'#skF_5')
      | v2_tex_2(B_643,'#skF_4')
      | ~ m1_subset_1(B_643,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7786,c_8750])).

tff(c_8763,plain,(
    ! [B_643] :
      ( m1_subset_1('#skF_3'('#skF_4',B_643),'#skF_5')
      | v2_tex_2(B_643,'#skF_4')
      | ~ m1_subset_1(B_643,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_7786,c_8759])).

tff(c_8765,plain,(
    ! [B_644] :
      ( m1_subset_1('#skF_3'('#skF_4',B_644),'#skF_5')
      | v2_tex_2(B_644,'#skF_4')
      | ~ m1_subset_1(B_644,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8763])).

tff(c_8768,plain,(
    ! [B_644] :
      ( k6_domain_1('#skF_5','#skF_3'('#skF_4',B_644)) = k1_tarski('#skF_3'('#skF_4',B_644))
      | v1_xboole_0('#skF_5')
      | v2_tex_2(B_644,'#skF_4')
      | ~ m1_subset_1(B_644,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8765,c_34])).

tff(c_10810,plain,(
    ! [B_795] :
      ( k6_domain_1('#skF_5','#skF_3'('#skF_4',B_795)) = k1_tarski('#skF_3'('#skF_4',B_795))
      | v2_tex_2(B_795,'#skF_4')
      | ~ m1_subset_1(B_795,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7860,c_8768])).

tff(c_10832,plain,
    ( k6_domain_1('#skF_5','#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_7803,c_10810])).

tff(c_10856,plain,(
    k6_domain_1('#skF_5','#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10832])).

tff(c_7802,plain,(
    ! [C_45] :
      ( k9_subset_1('#skF_5','#skF_5',k2_pre_topc('#skF_4',k6_domain_1('#skF_5',C_45))) = k6_domain_1('#skF_5',C_45)
      | ~ r2_hidden(C_45,'#skF_5')
      | ~ m1_subset_1(C_45,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7786,c_7786,c_7786,c_7786,c_54])).

tff(c_8071,plain,(
    ! [A_582,B_583] :
      ( v4_pre_topc(k2_pre_topc(A_582,B_583),A_582)
      | ~ m1_subset_1(B_583,k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ l1_pre_topc(A_582)
      | ~ v2_pre_topc(A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8078,plain,(
    ! [B_583] :
      ( v4_pre_topc(k2_pre_topc('#skF_4',B_583),'#skF_4')
      | ~ m1_subset_1(B_583,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7786,c_8071])).

tff(c_8088,plain,(
    ! [B_583] :
      ( v4_pre_topc(k2_pre_topc('#skF_4',B_583),'#skF_4')
      | ~ m1_subset_1(B_583,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_8078])).

tff(c_8160,plain,(
    ! [A_595,B_596] :
      ( m1_subset_1(k2_pre_topc(A_595,B_596),k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ l1_pre_topc(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8176,plain,(
    ! [B_596] :
      ( m1_subset_1(k2_pre_topc('#skF_4',B_596),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7786,c_8160])).

tff(c_8183,plain,(
    ! [B_596] :
      ( m1_subset_1(k2_pre_topc('#skF_4',B_596),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(B_596,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7786,c_8176])).

tff(c_8362,plain,(
    ! [B_612,A_613] :
      ( v3_pre_topc(B_612,A_613)
      | ~ v4_pre_topc(B_612,A_613)
      | ~ m1_subset_1(B_612,k1_zfmisc_1(u1_struct_0(A_613)))
      | ~ v3_tdlat_3(A_613)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8375,plain,(
    ! [B_612] :
      ( v3_pre_topc(B_612,'#skF_4')
      | ~ v4_pre_topc(B_612,'#skF_4')
      | ~ m1_subset_1(B_612,k1_zfmisc_1('#skF_5'))
      | ~ v3_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7786,c_8362])).

tff(c_8391,plain,(
    ! [B_614] :
      ( v3_pre_topc(B_614,'#skF_4')
      | ~ v4_pre_topc(B_614,'#skF_4')
      | ~ m1_subset_1(B_614,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_60,c_8375])).

tff(c_9244,plain,(
    ! [B_684] :
      ( v3_pre_topc(k2_pre_topc('#skF_4',B_684),'#skF_4')
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',B_684),'#skF_4')
      | ~ m1_subset_1(B_684,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8183,c_8391])).

tff(c_9262,plain,(
    ! [B_583] :
      ( v3_pre_topc(k2_pre_topc('#skF_4',B_583),'#skF_4')
      | ~ m1_subset_1(B_583,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8088,c_9244])).

tff(c_8881,plain,(
    ! [A_655,B_656,D_657] :
      ( k9_subset_1(u1_struct_0(A_655),B_656,D_657) != k6_domain_1(u1_struct_0(A_655),'#skF_3'(A_655,B_656))
      | ~ v3_pre_topc(D_657,A_655)
      | ~ m1_subset_1(D_657,k1_zfmisc_1(u1_struct_0(A_655)))
      | v2_tex_2(B_656,A_655)
      | ~ m1_subset_1(B_656,k1_zfmisc_1(u1_struct_0(A_655)))
      | ~ l1_pre_topc(A_655)
      | ~ v2_pre_topc(A_655)
      | v2_struct_0(A_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8885,plain,(
    ! [B_656,D_657] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_656,D_657) != k6_domain_1('#skF_5','#skF_3'('#skF_4',B_656))
      | ~ v3_pre_topc(D_657,'#skF_4')
      | ~ m1_subset_1(D_657,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_656,'#skF_4')
      | ~ m1_subset_1(B_656,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7786,c_8881])).

tff(c_8890,plain,(
    ! [B_656,D_657] :
      ( k9_subset_1('#skF_5',B_656,D_657) != k6_domain_1('#skF_5','#skF_3'('#skF_4',B_656))
      | ~ v3_pre_topc(D_657,'#skF_4')
      | ~ m1_subset_1(D_657,k1_zfmisc_1('#skF_5'))
      | v2_tex_2(B_656,'#skF_4')
      | ~ m1_subset_1(B_656,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_7786,c_7786,c_7786,c_8885])).

tff(c_8891,plain,(
    ! [B_656,D_657] :
      ( k9_subset_1('#skF_5',B_656,D_657) != k6_domain_1('#skF_5','#skF_3'('#skF_4',B_656))
      | ~ v3_pre_topc(D_657,'#skF_4')
      | ~ m1_subset_1(D_657,k1_zfmisc_1('#skF_5'))
      | v2_tex_2(B_656,'#skF_4')
      | ~ m1_subset_1(B_656,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8890])).

tff(c_10862,plain,(
    ! [D_657] :
      ( k9_subset_1('#skF_5','#skF_5',D_657) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ v3_pre_topc(D_657,'#skF_4')
      | ~ m1_subset_1(D_657,k1_zfmisc_1('#skF_5'))
      | v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10856,c_8891])).

tff(c_10869,plain,(
    ! [D_657] :
      ( k9_subset_1('#skF_5','#skF_5',D_657) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ v3_pre_topc(D_657,'#skF_4')
      | ~ m1_subset_1(D_657,k1_zfmisc_1('#skF_5'))
      | v2_tex_2('#skF_5','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7803,c_10862])).

tff(c_10901,plain,(
    ! [D_797] :
      ( k9_subset_1('#skF_5','#skF_5',D_797) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ v3_pre_topc(D_797,'#skF_4')
      | ~ m1_subset_1(D_797,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10869])).

tff(c_11037,plain,(
    ! [B_803] :
      ( k9_subset_1('#skF_5','#skF_5',k2_pre_topc('#skF_4',B_803)) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_4',B_803),'#skF_4')
      | ~ m1_subset_1(B_803,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8183,c_10901])).

tff(c_11046,plain,(
    ! [B_804] :
      ( k9_subset_1('#skF_5','#skF_5',k2_pre_topc('#skF_4',B_804)) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_804,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_9262,c_11037])).

tff(c_11093,plain,(
    ! [A_805] :
      ( k9_subset_1('#skF_5','#skF_5',k2_pre_topc('#skF_4',A_805)) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ r1_tarski(A_805,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_11046])).

tff(c_11333,plain,(
    ! [C_816] :
      ( k6_domain_1('#skF_5',C_816) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ r1_tarski(k6_domain_1('#skF_5',C_816),'#skF_5')
      | ~ r2_hidden(C_816,'#skF_5')
      | ~ m1_subset_1(C_816,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7802,c_11093])).

tff(c_11339,plain,
    ( k6_domain_1('#skF_5','#skF_3'('#skF_4','#skF_5')) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10856,c_11333])).

tff(c_11349,plain,
    ( ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_11339])).

tff(c_15212,plain,(
    ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_11349])).

tff(c_15215,plain,
    ( v1_xboole_0('#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8558,c_15212])).

tff(c_15224,plain,
    ( v1_xboole_0('#skF_5')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7803,c_15215])).

tff(c_15226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7860,c_15224])).

tff(c_15227,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_11349])).

tff(c_15270,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_15227])).

tff(c_15280,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_15270])).

tff(c_15286,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8528,c_15280])).

tff(c_15299,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7786,c_62,c_58,c_15286])).

tff(c_15301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_15299])).

tff(c_15302,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_15227])).

tff(c_15309,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8528,c_15302])).

tff(c_15322,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7786,c_62,c_58,c_15309])).

tff(c_15324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_15322])).

tff(c_15325,plain,(
    ! [A_547] : ~ r2_hidden(A_547,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_7857])).

tff(c_16093,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16080,c_15325])).

tff(c_16104,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7803,c_16093])).

tff(c_16106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_16104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.91/3.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.51  
% 9.21/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.51  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 9.21/3.51  
% 9.21/3.51  %Foreground sorts:
% 9.21/3.51  
% 9.21/3.51  
% 9.21/3.51  %Background operators:
% 9.21/3.51  
% 9.21/3.51  
% 9.21/3.51  %Foreground operators:
% 9.21/3.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.21/3.51  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.21/3.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.21/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.21/3.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.21/3.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.21/3.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.21/3.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.21/3.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.21/3.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.21/3.51  tff('#skF_5', type, '#skF_5': $i).
% 9.21/3.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.21/3.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.21/3.51  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 9.21/3.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.21/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.21/3.51  tff('#skF_4', type, '#skF_4': $i).
% 9.21/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.21/3.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.21/3.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.21/3.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.21/3.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.21/3.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.21/3.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.21/3.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.21/3.51  
% 9.27/3.54  tff(f_148, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 9.27/3.54  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 9.27/3.54  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.27/3.54  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.27/3.54  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.27/3.54  tff(f_66, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.27/3.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.27/3.54  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.27/3.54  tff(f_87, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 9.27/3.54  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.27/3.54  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.27/3.54  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 9.27/3.54  tff(c_52, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.27/3.54  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.27/3.54  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.27/3.54  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.27/3.54  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.27/3.54  tff(c_2288, plain, (![A_286, B_287]: (r2_hidden('#skF_3'(A_286, B_287), B_287) | v2_tex_2(B_287, A_286) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.27/3.54  tff(c_2303, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2288])).
% 9.27/3.54  tff(c_2311, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2303])).
% 9.27/3.54  tff(c_2312, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_2311])).
% 9.27/3.54  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.27/3.54  tff(c_93, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | ~r1_tarski(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.27/3.54  tff(c_102, plain, (![A_56]: (r2_hidden(A_56, k1_tarski(A_56)))), inference(resolution, [status(thm)], [c_12, c_93])).
% 9.27/3.54  tff(c_28, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.27/3.54  tff(c_176, plain, (![C_79, B_80, A_81]: (~v1_xboole_0(C_79) | ~m1_subset_1(B_80, k1_zfmisc_1(C_79)) | ~r2_hidden(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.27/3.54  tff(c_188, plain, (![B_82, A_83, A_84]: (~v1_xboole_0(B_82) | ~r2_hidden(A_83, A_84) | ~r1_tarski(A_84, B_82))), inference(resolution, [status(thm)], [c_28, c_176])).
% 9.27/3.54  tff(c_198, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | ~r1_tarski(k1_tarski(A_86), B_85))), inference(resolution, [status(thm)], [c_102, c_188])).
% 9.27/3.54  tff(c_207, plain, (![A_86]: (~v1_xboole_0(k1_tarski(A_86)))), inference(resolution, [status(thm)], [c_12, c_198])).
% 9.27/3.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.54  tff(c_146, plain, (![B_69, A_70]: (m1_subset_1(B_69, A_70) | ~r2_hidden(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.27/3.54  tff(c_156, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_146])).
% 9.27/3.54  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.27/3.54  tff(c_20, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.27/3.54  tff(c_159, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.54  tff(c_412, plain, (![B_116, B_117, A_118]: (r2_hidden(B_116, B_117) | ~r1_tarski(A_118, B_117) | ~m1_subset_1(B_116, A_118) | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_20, c_159])).
% 9.27/3.54  tff(c_420, plain, (![B_116, B_9, A_8]: (r2_hidden(B_116, B_9) | ~m1_subset_1(B_116, k1_tarski(A_8)) | v1_xboole_0(k1_tarski(A_8)) | ~r2_hidden(A_8, B_9))), inference(resolution, [status(thm)], [c_16, c_412])).
% 9.27/3.54  tff(c_2013, plain, (![B_255, B_256, A_257]: (r2_hidden(B_255, B_256) | ~m1_subset_1(B_255, k1_tarski(A_257)) | ~r2_hidden(A_257, B_256))), inference(negUnitSimplification, [status(thm)], [c_207, c_420])).
% 9.27/3.54  tff(c_2016, plain, (![A_257, B_2, B_256]: (r2_hidden('#skF_1'(k1_tarski(A_257), B_2), B_256) | ~r2_hidden(A_257, B_256) | v1_xboole_0(k1_tarski(A_257)) | r1_tarski(k1_tarski(A_257), B_2))), inference(resolution, [status(thm)], [c_156, c_2013])).
% 9.27/3.54  tff(c_4084, plain, (![A_386, B_387, B_388]: (r2_hidden('#skF_1'(k1_tarski(A_386), B_387), B_388) | ~r2_hidden(A_386, B_388) | r1_tarski(k1_tarski(A_386), B_387))), inference(negUnitSimplification, [status(thm)], [c_207, c_2016])).
% 9.27/3.54  tff(c_186, plain, (![A_81]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_81, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_176])).
% 9.27/3.54  tff(c_187, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_186])).
% 9.27/3.54  tff(c_103, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.27/3.54  tff(c_116, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_103])).
% 9.27/3.54  tff(c_425, plain, (![B_116]: (r2_hidden(B_116, u1_struct_0('#skF_4')) | ~m1_subset_1(B_116, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_116, c_412])).
% 9.27/3.54  tff(c_430, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_425])).
% 9.27/3.54  tff(c_741, plain, (![A_151, B_152]: (r2_hidden('#skF_3'(A_151, B_152), B_152) | v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.27/3.54  tff(c_756, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_741])).
% 9.27/3.54  tff(c_764, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_756])).
% 9.27/3.54  tff(c_765, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_764])).
% 9.27/3.54  tff(c_206, plain, (![B_9, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_8, B_9))), inference(resolution, [status(thm)], [c_16, c_198])).
% 9.27/3.54  tff(c_768, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_765, c_206])).
% 9.27/3.54  tff(c_779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_430, c_768])).
% 9.27/3.54  tff(c_781, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_425])).
% 9.27/3.54  tff(c_2048, plain, (![A_261, B_262, B_263]: (r2_hidden('#skF_1'(A_261, B_262), B_263) | ~r1_tarski(A_261, B_263) | r1_tarski(A_261, B_262))), inference(resolution, [status(thm)], [c_6, c_159])).
% 9.27/3.54  tff(c_18, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.27/3.54  tff(c_2817, plain, (![A_319, B_320, B_321]: (m1_subset_1('#skF_1'(A_319, B_320), B_321) | v1_xboole_0(B_321) | ~r1_tarski(A_319, B_321) | r1_tarski(A_319, B_320))), inference(resolution, [status(thm)], [c_2048, c_18])).
% 9.27/3.54  tff(c_782, plain, (![B_153]: (r2_hidden(B_153, u1_struct_0('#skF_4')) | ~m1_subset_1(B_153, '#skF_5'))), inference(splitRight, [status(thm)], [c_425])).
% 9.27/3.54  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.54  tff(c_803, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_782, c_4])).
% 9.27/3.54  tff(c_2838, plain, (![A_319]: (v1_xboole_0('#skF_5') | ~r1_tarski(A_319, '#skF_5') | r1_tarski(A_319, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2817, c_803])).
% 9.27/3.54  tff(c_2890, plain, (![A_324]: (~r1_tarski(A_324, '#skF_5') | r1_tarski(A_324, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_781, c_2838])).
% 9.27/3.54  tff(c_14, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | ~r1_tarski(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.27/3.54  tff(c_2957, plain, (![A_325]: (r2_hidden(A_325, u1_struct_0('#skF_4')) | ~r1_tarski(k1_tarski(A_325), '#skF_5'))), inference(resolution, [status(thm)], [c_2890, c_14])).
% 9.27/3.54  tff(c_2967, plain, (![A_325]: (m1_subset_1(A_325, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(k1_tarski(A_325), '#skF_5'))), inference(resolution, [status(thm)], [c_2957, c_18])).
% 9.27/3.54  tff(c_2979, plain, (![A_326]: (m1_subset_1(A_326, u1_struct_0('#skF_4')) | ~r1_tarski(k1_tarski(A_326), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_2967])).
% 9.27/3.54  tff(c_2989, plain, (![A_327]: (m1_subset_1(A_327, u1_struct_0('#skF_4')) | ~r2_hidden(A_327, '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_2979])).
% 9.27/3.54  tff(c_134, plain, (![A_67, B_68]: (~r2_hidden('#skF_1'(A_67, B_68), B_68) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.54  tff(c_145, plain, (![A_67, A_10]: (r1_tarski(A_67, A_10) | ~m1_subset_1('#skF_1'(A_67, A_10), A_10) | v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_20, c_134])).
% 9.27/3.54  tff(c_2993, plain, (![A_67]: (r1_tarski(A_67, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_67, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_2989, c_145])).
% 9.27/3.54  tff(c_3002, plain, (![A_67]: (r1_tarski(A_67, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_67, u1_struct_0('#skF_4')), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_2993])).
% 9.27/3.54  tff(c_4118, plain, (![A_386]: (~r2_hidden(A_386, '#skF_5') | r1_tarski(k1_tarski(A_386), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4084, c_3002])).
% 9.27/3.54  tff(c_2153, plain, (![A_273, B_274]: (v4_pre_topc(k2_pre_topc(A_273, B_274), A_273) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.27/3.54  tff(c_2172, plain, (![A_273, A_12]: (v4_pre_topc(k2_pre_topc(A_273, A_12), A_273) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | ~r1_tarski(A_12, u1_struct_0(A_273)))), inference(resolution, [status(thm)], [c_28, c_2153])).
% 9.27/3.54  tff(c_32, plain, (![A_17, B_18]: (m1_subset_1(k2_pre_topc(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.27/3.54  tff(c_2322, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2312, c_18])).
% 9.27/3.54  tff(c_2328, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_781, c_2322])).
% 9.27/3.54  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.54  tff(c_2354, plain, (![B_289]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_289) | ~r1_tarski('#skF_5', B_289))), inference(resolution, [status(thm)], [c_2312, c_2])).
% 9.27/3.54  tff(c_2457, plain, (![B_295, B_296]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_295) | ~r1_tarski(B_296, B_295) | ~r1_tarski('#skF_5', B_296))), inference(resolution, [status(thm)], [c_2354, c_2])).
% 9.27/3.54  tff(c_2463, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_116, c_2457])).
% 9.27/3.54  tff(c_2472, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2463])).
% 9.27/3.54  tff(c_2484, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2472, c_18])).
% 9.27/3.54  tff(c_2490, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_187, c_2484])).
% 9.27/3.54  tff(c_34, plain, (![A_19, B_20]: (k6_domain_1(A_19, B_20)=k1_tarski(B_20) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.27/3.54  tff(c_2493, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2490, c_34])).
% 9.27/3.54  tff(c_2499, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_2493])).
% 9.27/3.54  tff(c_2414, plain, (![B_294]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), B_294) | v1_xboole_0(B_294) | ~r1_tarski('#skF_5', B_294))), inference(resolution, [status(thm)], [c_2354, c_18])).
% 9.27/3.54  tff(c_6993, plain, (![B_493]: (k6_domain_1(B_493, '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0(B_493) | ~r1_tarski('#skF_5', B_493))), inference(resolution, [status(thm)], [c_2414, c_34])).
% 9.27/3.54  tff(c_54, plain, (![C_45]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_45)))=k6_domain_1(u1_struct_0('#skF_4'), C_45) | ~r2_hidden(C_45, '#skF_5') | ~m1_subset_1(C_45, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.27/3.54  tff(c_7048, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))))=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6993, c_54])).
% 9.27/3.54  tff(c_7137, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))))=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_2490, c_2312, c_2499, c_7048])).
% 9.27/3.54  tff(c_7138, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))))=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_7137])).
% 9.27/3.54  tff(c_792, plain, (![B_153]: (m1_subset_1(B_153, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_153, '#skF_5'))), inference(resolution, [status(thm)], [c_782, c_18])).
% 9.27/3.54  tff(c_804, plain, (![B_154]: (m1_subset_1(B_154, u1_struct_0('#skF_4')) | ~m1_subset_1(B_154, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_792])).
% 9.27/3.54  tff(c_811, plain, (![B_154]: (k6_domain_1(u1_struct_0('#skF_4'), B_154)=k1_tarski(B_154) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_154, '#skF_5'))), inference(resolution, [status(thm)], [c_804, c_34])).
% 9.27/3.54  tff(c_820, plain, (![B_154]: (k6_domain_1(u1_struct_0('#skF_4'), B_154)=k1_tarski(B_154) | ~m1_subset_1(B_154, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_811])).
% 9.27/3.54  tff(c_2580, plain, (![A_301, B_302, D_303]: (k9_subset_1(u1_struct_0(A_301), B_302, D_303)!=k6_domain_1(u1_struct_0(A_301), '#skF_3'(A_301, B_302)) | ~v3_pre_topc(D_303, A_301) | ~m1_subset_1(D_303, k1_zfmisc_1(u1_struct_0(A_301))) | v2_tex_2(B_302, A_301) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.27/3.54  tff(c_2587, plain, (![B_302, D_303]: (k9_subset_1(u1_struct_0('#skF_4'), B_302, D_303)!=k1_tarski('#skF_3'('#skF_4', B_302)) | ~v3_pre_topc(D_303, '#skF_4') | ~m1_subset_1(D_303, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_302, '#skF_4') | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3'('#skF_4', B_302), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_820, c_2580])).
% 9.27/3.54  tff(c_2597, plain, (![B_302, D_303]: (k9_subset_1(u1_struct_0('#skF_4'), B_302, D_303)!=k1_tarski('#skF_3'('#skF_4', B_302)) | ~v3_pre_topc(D_303, '#skF_4') | ~m1_subset_1(D_303, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_302, '#skF_4') | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3'('#skF_4', B_302), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2587])).
% 9.27/3.54  tff(c_2598, plain, (![B_302, D_303]: (k9_subset_1(u1_struct_0('#skF_4'), B_302, D_303)!=k1_tarski('#skF_3'('#skF_4', B_302)) | ~v3_pre_topc(D_303, '#skF_4') | ~m1_subset_1(D_303, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_302, '#skF_4') | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_3'('#skF_4', B_302), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_2597])).
% 9.27/3.54  tff(c_7374, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7138, c_2598])).
% 9.27/3.54  tff(c_7404, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2328, c_56, c_7374])).
% 9.27/3.54  tff(c_7405, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_7404])).
% 9.27/3.54  tff(c_7422, plain, (~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_7405])).
% 9.27/3.54  tff(c_7431, plain, (~m1_subset_1(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_7422])).
% 9.27/3.54  tff(c_7442, plain, (~m1_subset_1(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7431])).
% 9.27/3.54  tff(c_7459, plain, (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_7442])).
% 9.27/3.54  tff(c_7463, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_4118, c_7459])).
% 9.27/3.54  tff(c_7479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2312, c_7463])).
% 9.27/3.54  tff(c_7480, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(splitRight, [status(thm)], [c_7405])).
% 9.27/3.54  tff(c_60, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.27/3.54  tff(c_7481, plain, (m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_7405])).
% 9.27/3.54  tff(c_38, plain, (![B_26, A_23]: (v3_pre_topc(B_26, A_23) | ~v4_pre_topc(B_26, A_23) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_23))) | ~v3_tdlat_3(A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.27/3.54  tff(c_7516, plain, (v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_7481, c_38])).
% 9.27/3.54  tff(c_7557, plain, (v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_60, c_7516])).
% 9.27/3.54  tff(c_7558, plain, (~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_7480, c_7557])).
% 9.27/3.54  tff(c_7623, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2172, c_7558])).
% 9.27/3.54  tff(c_7628, plain, (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_7623])).
% 9.27/3.54  tff(c_7631, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_4118, c_7628])).
% 9.27/3.54  tff(c_7647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2312, c_7631])).
% 9.27/3.54  tff(c_7649, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_186])).
% 9.27/3.54  tff(c_7715, plain, (![B_521, A_522, A_523]: (~v1_xboole_0(B_521) | ~r2_hidden(A_522, A_523) | ~r1_tarski(A_523, B_521))), inference(resolution, [status(thm)], [c_28, c_176])).
% 9.27/3.54  tff(c_7726, plain, (![B_525, A_526]: (~v1_xboole_0(B_525) | ~r1_tarski(k1_tarski(A_526), B_525))), inference(resolution, [status(thm)], [c_102, c_7715])).
% 9.27/3.54  tff(c_7749, plain, (![B_529, A_530]: (~v1_xboole_0(B_529) | ~r2_hidden(A_530, B_529))), inference(resolution, [status(thm)], [c_16, c_7726])).
% 9.27/3.54  tff(c_7762, plain, (![A_531, B_532]: (~v1_xboole_0(A_531) | r1_tarski(A_531, B_532))), inference(resolution, [status(thm)], [c_6, c_7749])).
% 9.27/3.54  tff(c_120, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.27/3.54  tff(c_127, plain, (u1_struct_0('#skF_4')='#skF_5' | ~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_116, c_120])).
% 9.27/3.54  tff(c_133, plain, (~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_127])).
% 9.27/3.54  tff(c_7773, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_7762, c_133])).
% 9.27/3.54  tff(c_7785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7649, c_7773])).
% 9.27/3.54  tff(c_7786, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_127])).
% 9.27/3.54  tff(c_7803, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7786, c_56])).
% 9.27/3.54  tff(c_16023, plain, (![A_1074, B_1075]: (r2_hidden('#skF_3'(A_1074, B_1075), B_1075) | v2_tex_2(B_1075, A_1074) | ~m1_subset_1(B_1075, k1_zfmisc_1(u1_struct_0(A_1074))) | ~l1_pre_topc(A_1074) | ~v2_pre_topc(A_1074) | v2_struct_0(A_1074))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.27/3.54  tff(c_16032, plain, (![B_1075]: (r2_hidden('#skF_3'('#skF_4', B_1075), B_1075) | v2_tex_2(B_1075, '#skF_4') | ~m1_subset_1(B_1075, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7786, c_16023])).
% 9.27/3.54  tff(c_16043, plain, (![B_1075]: (r2_hidden('#skF_3'('#skF_4', B_1075), B_1075) | v2_tex_2(B_1075, '#skF_4') | ~m1_subset_1(B_1075, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_16032])).
% 9.27/3.54  tff(c_16080, plain, (![B_1082]: (r2_hidden('#skF_3'('#skF_4', B_1082), B_1082) | v2_tex_2(B_1082, '#skF_4') | ~m1_subset_1(B_1082, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_16043])).
% 9.27/3.54  tff(c_8506, plain, (![A_624, B_625]: (r2_hidden('#skF_3'(A_624, B_625), B_625) | v2_tex_2(B_625, A_624) | ~m1_subset_1(B_625, k1_zfmisc_1(u1_struct_0(A_624))) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.27/3.54  tff(c_8528, plain, (![A_624, A_12]: (r2_hidden('#skF_3'(A_624, A_12), A_12) | v2_tex_2(A_12, A_624) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624) | ~r1_tarski(A_12, u1_struct_0(A_624)))), inference(resolution, [status(thm)], [c_28, c_8506])).
% 9.27/3.54  tff(c_7849, plain, (![C_545, B_546, A_547]: (~v1_xboole_0(C_545) | ~m1_subset_1(B_546, k1_zfmisc_1(C_545)) | ~r2_hidden(A_547, B_546))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.27/3.54  tff(c_7857, plain, (![A_547]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_547, '#skF_5'))), inference(resolution, [status(thm)], [c_7803, c_7849])).
% 9.27/3.54  tff(c_7860, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_7857])).
% 9.27/3.54  tff(c_8515, plain, (![B_625]: (r2_hidden('#skF_3'('#skF_4', B_625), B_625) | v2_tex_2(B_625, '#skF_4') | ~m1_subset_1(B_625, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7786, c_8506])).
% 9.27/3.54  tff(c_8526, plain, (![B_625]: (r2_hidden('#skF_3'('#skF_4', B_625), B_625) | v2_tex_2(B_625, '#skF_4') | ~m1_subset_1(B_625, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_8515])).
% 9.27/3.54  tff(c_8530, plain, (![B_626]: (r2_hidden('#skF_3'('#skF_4', B_626), B_626) | v2_tex_2(B_626, '#skF_4') | ~m1_subset_1(B_626, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8526])).
% 9.27/3.54  tff(c_8558, plain, (![B_626]: (m1_subset_1('#skF_3'('#skF_4', B_626), B_626) | v1_xboole_0(B_626) | v2_tex_2(B_626, '#skF_4') | ~m1_subset_1(B_626, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_8530, c_18])).
% 9.27/3.54  tff(c_8750, plain, (![A_642, B_643]: (m1_subset_1('#skF_3'(A_642, B_643), u1_struct_0(A_642)) | v2_tex_2(B_643, A_642) | ~m1_subset_1(B_643, k1_zfmisc_1(u1_struct_0(A_642))) | ~l1_pre_topc(A_642) | ~v2_pre_topc(A_642) | v2_struct_0(A_642))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.27/3.54  tff(c_8759, plain, (![B_643]: (m1_subset_1('#skF_3'('#skF_4', B_643), '#skF_5') | v2_tex_2(B_643, '#skF_4') | ~m1_subset_1(B_643, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7786, c_8750])).
% 9.27/3.54  tff(c_8763, plain, (![B_643]: (m1_subset_1('#skF_3'('#skF_4', B_643), '#skF_5') | v2_tex_2(B_643, '#skF_4') | ~m1_subset_1(B_643, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_7786, c_8759])).
% 9.27/3.54  tff(c_8765, plain, (![B_644]: (m1_subset_1('#skF_3'('#skF_4', B_644), '#skF_5') | v2_tex_2(B_644, '#skF_4') | ~m1_subset_1(B_644, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8763])).
% 9.27/3.54  tff(c_8768, plain, (![B_644]: (k6_domain_1('#skF_5', '#skF_3'('#skF_4', B_644))=k1_tarski('#skF_3'('#skF_4', B_644)) | v1_xboole_0('#skF_5') | v2_tex_2(B_644, '#skF_4') | ~m1_subset_1(B_644, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_8765, c_34])).
% 9.27/3.54  tff(c_10810, plain, (![B_795]: (k6_domain_1('#skF_5', '#skF_3'('#skF_4', B_795))=k1_tarski('#skF_3'('#skF_4', B_795)) | v2_tex_2(B_795, '#skF_4') | ~m1_subset_1(B_795, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_7860, c_8768])).
% 9.27/3.54  tff(c_10832, plain, (k6_domain_1('#skF_5', '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_7803, c_10810])).
% 9.27/3.54  tff(c_10856, plain, (k6_domain_1('#skF_5', '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_10832])).
% 9.27/3.54  tff(c_7802, plain, (![C_45]: (k9_subset_1('#skF_5', '#skF_5', k2_pre_topc('#skF_4', k6_domain_1('#skF_5', C_45)))=k6_domain_1('#skF_5', C_45) | ~r2_hidden(C_45, '#skF_5') | ~m1_subset_1(C_45, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7786, c_7786, c_7786, c_7786, c_54])).
% 9.27/3.54  tff(c_8071, plain, (![A_582, B_583]: (v4_pre_topc(k2_pre_topc(A_582, B_583), A_582) | ~m1_subset_1(B_583, k1_zfmisc_1(u1_struct_0(A_582))) | ~l1_pre_topc(A_582) | ~v2_pre_topc(A_582))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.27/3.54  tff(c_8078, plain, (![B_583]: (v4_pre_topc(k2_pre_topc('#skF_4', B_583), '#skF_4') | ~m1_subset_1(B_583, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7786, c_8071])).
% 9.27/3.54  tff(c_8088, plain, (![B_583]: (v4_pre_topc(k2_pre_topc('#skF_4', B_583), '#skF_4') | ~m1_subset_1(B_583, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_8078])).
% 9.27/3.54  tff(c_8160, plain, (![A_595, B_596]: (m1_subset_1(k2_pre_topc(A_595, B_596), k1_zfmisc_1(u1_struct_0(A_595))) | ~m1_subset_1(B_596, k1_zfmisc_1(u1_struct_0(A_595))) | ~l1_pre_topc(A_595))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.27/3.54  tff(c_8176, plain, (![B_596]: (m1_subset_1(k2_pre_topc('#skF_4', B_596), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(B_596, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7786, c_8160])).
% 9.27/3.54  tff(c_8183, plain, (![B_596]: (m1_subset_1(k2_pre_topc('#skF_4', B_596), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(B_596, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7786, c_8176])).
% 9.27/3.54  tff(c_8362, plain, (![B_612, A_613]: (v3_pre_topc(B_612, A_613) | ~v4_pre_topc(B_612, A_613) | ~m1_subset_1(B_612, k1_zfmisc_1(u1_struct_0(A_613))) | ~v3_tdlat_3(A_613) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.27/3.54  tff(c_8375, plain, (![B_612]: (v3_pre_topc(B_612, '#skF_4') | ~v4_pre_topc(B_612, '#skF_4') | ~m1_subset_1(B_612, k1_zfmisc_1('#skF_5')) | ~v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7786, c_8362])).
% 9.27/3.54  tff(c_8391, plain, (![B_614]: (v3_pre_topc(B_614, '#skF_4') | ~v4_pre_topc(B_614, '#skF_4') | ~m1_subset_1(B_614, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_60, c_8375])).
% 9.27/3.54  tff(c_9244, plain, (![B_684]: (v3_pre_topc(k2_pre_topc('#skF_4', B_684), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', B_684), '#skF_4') | ~m1_subset_1(B_684, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_8183, c_8391])).
% 9.27/3.54  tff(c_9262, plain, (![B_583]: (v3_pre_topc(k2_pre_topc('#skF_4', B_583), '#skF_4') | ~m1_subset_1(B_583, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_8088, c_9244])).
% 9.27/3.54  tff(c_8881, plain, (![A_655, B_656, D_657]: (k9_subset_1(u1_struct_0(A_655), B_656, D_657)!=k6_domain_1(u1_struct_0(A_655), '#skF_3'(A_655, B_656)) | ~v3_pre_topc(D_657, A_655) | ~m1_subset_1(D_657, k1_zfmisc_1(u1_struct_0(A_655))) | v2_tex_2(B_656, A_655) | ~m1_subset_1(B_656, k1_zfmisc_1(u1_struct_0(A_655))) | ~l1_pre_topc(A_655) | ~v2_pre_topc(A_655) | v2_struct_0(A_655))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.27/3.54  tff(c_8885, plain, (![B_656, D_657]: (k9_subset_1(u1_struct_0('#skF_4'), B_656, D_657)!=k6_domain_1('#skF_5', '#skF_3'('#skF_4', B_656)) | ~v3_pre_topc(D_657, '#skF_4') | ~m1_subset_1(D_657, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_656, '#skF_4') | ~m1_subset_1(B_656, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7786, c_8881])).
% 9.27/3.54  tff(c_8890, plain, (![B_656, D_657]: (k9_subset_1('#skF_5', B_656, D_657)!=k6_domain_1('#skF_5', '#skF_3'('#skF_4', B_656)) | ~v3_pre_topc(D_657, '#skF_4') | ~m1_subset_1(D_657, k1_zfmisc_1('#skF_5')) | v2_tex_2(B_656, '#skF_4') | ~m1_subset_1(B_656, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_7786, c_7786, c_7786, c_8885])).
% 9.27/3.54  tff(c_8891, plain, (![B_656, D_657]: (k9_subset_1('#skF_5', B_656, D_657)!=k6_domain_1('#skF_5', '#skF_3'('#skF_4', B_656)) | ~v3_pre_topc(D_657, '#skF_4') | ~m1_subset_1(D_657, k1_zfmisc_1('#skF_5')) | v2_tex_2(B_656, '#skF_4') | ~m1_subset_1(B_656, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8890])).
% 9.27/3.54  tff(c_10862, plain, (![D_657]: (k9_subset_1('#skF_5', '#skF_5', D_657)!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(D_657, '#skF_4') | ~m1_subset_1(D_657, k1_zfmisc_1('#skF_5')) | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10856, c_8891])).
% 9.27/3.54  tff(c_10869, plain, (![D_657]: (k9_subset_1('#skF_5', '#skF_5', D_657)!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(D_657, '#skF_4') | ~m1_subset_1(D_657, k1_zfmisc_1('#skF_5')) | v2_tex_2('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7803, c_10862])).
% 9.27/3.54  tff(c_10901, plain, (![D_797]: (k9_subset_1('#skF_5', '#skF_5', D_797)!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(D_797, '#skF_4') | ~m1_subset_1(D_797, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_10869])).
% 9.27/3.54  tff(c_11037, plain, (![B_803]: (k9_subset_1('#skF_5', '#skF_5', k2_pre_topc('#skF_4', B_803))!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(k2_pre_topc('#skF_4', B_803), '#skF_4') | ~m1_subset_1(B_803, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_8183, c_10901])).
% 9.27/3.54  tff(c_11046, plain, (![B_804]: (k9_subset_1('#skF_5', '#skF_5', k2_pre_topc('#skF_4', B_804))!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1(B_804, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_9262, c_11037])).
% 9.27/3.54  tff(c_11093, plain, (![A_805]: (k9_subset_1('#skF_5', '#skF_5', k2_pre_topc('#skF_4', A_805))!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~r1_tarski(A_805, '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_11046])).
% 9.27/3.54  tff(c_11333, plain, (![C_816]: (k6_domain_1('#skF_5', C_816)!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~r1_tarski(k6_domain_1('#skF_5', C_816), '#skF_5') | ~r2_hidden(C_816, '#skF_5') | ~m1_subset_1(C_816, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7802, c_11093])).
% 9.27/3.54  tff(c_11339, plain, (k6_domain_1('#skF_5', '#skF_3'('#skF_4', '#skF_5'))!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), '#skF_5') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10856, c_11333])).
% 9.27/3.54  tff(c_11349, plain, (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), '#skF_5') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_11339])).
% 9.27/3.54  tff(c_15212, plain, (~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_11349])).
% 9.27/3.54  tff(c_15215, plain, (v1_xboole_0('#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_8558, c_15212])).
% 9.27/3.54  tff(c_15224, plain, (v1_xboole_0('#skF_5') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7803, c_15215])).
% 9.27/3.54  tff(c_15226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_7860, c_15224])).
% 9.27/3.54  tff(c_15227, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_11349])).
% 9.27/3.54  tff(c_15270, plain, (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_15227])).
% 9.27/3.54  tff(c_15280, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_16, c_15270])).
% 9.27/3.54  tff(c_15286, plain, (v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8528, c_15280])).
% 9.27/3.54  tff(c_15299, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_7786, c_62, c_58, c_15286])).
% 9.27/3.54  tff(c_15301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_15299])).
% 9.27/3.54  tff(c_15302, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_15227])).
% 9.27/3.54  tff(c_15309, plain, (v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8528, c_15302])).
% 9.27/3.54  tff(c_15322, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_7786, c_62, c_58, c_15309])).
% 9.27/3.54  tff(c_15324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_15322])).
% 9.27/3.54  tff(c_15325, plain, (![A_547]: (~r2_hidden(A_547, '#skF_5'))), inference(splitRight, [status(thm)], [c_7857])).
% 9.27/3.54  tff(c_16093, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_16080, c_15325])).
% 9.27/3.54  tff(c_16104, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7803, c_16093])).
% 9.27/3.54  tff(c_16106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_16104])).
% 9.27/3.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.54  
% 9.27/3.54  Inference rules
% 9.27/3.54  ----------------------
% 9.27/3.54  #Ref     : 0
% 9.27/3.54  #Sup     : 3627
% 9.27/3.54  #Fact    : 0
% 9.27/3.54  #Define  : 0
% 9.27/3.54  #Split   : 43
% 9.27/3.54  #Chain   : 0
% 9.27/3.54  #Close   : 0
% 9.27/3.54  
% 9.27/3.54  Ordering : KBO
% 9.27/3.54  
% 9.27/3.54  Simplification rules
% 9.27/3.54  ----------------------
% 9.27/3.54  #Subsume      : 1143
% 9.27/3.54  #Demod        : 799
% 9.27/3.54  #Tautology    : 874
% 9.27/3.54  #SimpNegUnit  : 534
% 9.27/3.54  #BackRed      : 41
% 9.27/3.54  
% 9.27/3.54  #Partial instantiations: 0
% 9.27/3.54  #Strategies tried      : 1
% 9.27/3.54  
% 9.27/3.54  Timing (in seconds)
% 9.27/3.54  ----------------------
% 9.27/3.54  Preprocessing        : 0.34
% 9.27/3.54  Parsing              : 0.18
% 9.27/3.54  CNF conversion       : 0.03
% 9.27/3.54  Main loop            : 2.40
% 9.27/3.54  Inferencing          : 0.73
% 9.27/3.54  Reduction            : 0.64
% 9.27/3.54  Demodulation         : 0.40
% 9.27/3.54  BG Simplification    : 0.07
% 9.27/3.54  Subsumption          : 0.76
% 9.27/3.54  Abstraction          : 0.11
% 9.27/3.54  MUC search           : 0.00
% 9.27/3.54  Cooper               : 0.00
% 9.27/3.54  Total                : 2.81
% 9.27/3.54  Index Insertion      : 0.00
% 9.27/3.54  Index Deletion       : 0.00
% 9.27/3.54  Index Matching       : 0.00
% 9.27/3.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
