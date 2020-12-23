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
% DateTime   : Thu Dec  3 10:30:19 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 328 expanded)
%              Number of leaves         :   35 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  307 (1240 expanded)
%              Number of equality atoms :   41 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( C != k1_xboole_0
                    & v3_pre_topc(C,A)
                    & r1_xboole_0(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v2_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( v3_pre_topc(B,A)
                & B != k1_xboole_0
                & B != u1_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tdlat_3)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_72,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_73,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_75,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_66])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_177,plain,(
    ! [A_62,B_63] :
      ( v3_pre_topc('#skF_1'(A_62,B_63),A_62)
      | v1_tops_1(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_184,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_177])).

tff(c_189,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_184])).

tff(c_190,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_203,plain,(
    ! [A_67,B_68] :
      ( '#skF_2'(A_67,B_68) != B_68
      | v3_tex_2(B_68,A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_213,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_203])).

tff(c_218,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_213])).

tff(c_219,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_218])).

tff(c_220,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_60,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_696,plain,(
    ! [B_126,A_127] :
      ( v2_tex_2(B_126,A_127)
      | ~ v1_zfmisc_1(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | v1_xboole_0(B_126)
      | ~ l1_pre_topc(A_127)
      | ~ v2_tdlat_3(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_712,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_696])).

tff(c_719,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_73,c_712])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_220,c_719])).

tff(c_723,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_895,plain,(
    ! [B_155,A_156] :
      ( v3_tex_2(B_155,A_156)
      | ~ v2_tex_2(B_155,A_156)
      | ~ v1_tops_1(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_908,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_895])).

tff(c_914,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_190,c_723,c_908])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_75,c_914])).

tff(c_918,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_949,plain,(
    ! [B_162,A_163] :
      ( r1_xboole_0(B_162,'#skF_1'(A_163,B_162))
      | v1_tops_1(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_956,plain,
    ( r1_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5'))
    | v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_949])).

tff(c_961,plain,
    ( r1_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5'))
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_956])).

tff(c_962,plain,(
    r1_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_961])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_966,plain,(
    k4_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_962,c_8])).

tff(c_144,plain,(
    ! [A_58,B_59] :
      ( '#skF_1'(A_58,B_59) != k1_xboole_0
      | v1_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_154,plain,
    ( '#skF_1'('#skF_4','#skF_5') != k1_xboole_0
    | v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_144])).

tff(c_159,plain,
    ( '#skF_1'('#skF_4','#skF_5') != k1_xboole_0
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_154])).

tff(c_160,plain,(
    '#skF_1'('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_917,plain,(
    v3_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_1087,plain,(
    ! [A_187,B_188] :
      ( m1_subset_1('#skF_1'(A_187,B_188),k1_zfmisc_1(u1_struct_0(A_187)))
      | v1_tops_1(B_188,A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1128,plain,(
    ! [A_191,B_192] :
      ( r1_tarski('#skF_1'(A_191,B_192),u1_struct_0(A_191))
      | v1_tops_1(B_192,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_1087,c_12])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1260,plain,(
    ! [A_207,B_208] :
      ( k4_xboole_0('#skF_1'(A_207,B_208),u1_struct_0(A_207)) = k1_xboole_0
      | v1_tops_1(B_208,A_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207) ) ),
    inference(resolution,[status(thm)],[c_1128,c_6])).

tff(c_1269,plain,
    ( k4_xboole_0('#skF_1'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) = k1_xboole_0
    | v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1260])).

tff(c_1275,plain,
    ( k4_xboole_0('#skF_1'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) = k1_xboole_0
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1269])).

tff(c_1276,plain,(
    k4_xboole_0('#skF_1'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_1275])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1156,plain,(
    ! [A_195,B_196] :
      ( u1_struct_0(A_195) = B_196
      | k1_xboole_0 = B_196
      | ~ v3_pre_topc(B_196,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ v2_tdlat_3(A_195)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1177,plain,(
    ! [A_197,A_198] :
      ( u1_struct_0(A_197) = A_198
      | k1_xboole_0 = A_198
      | ~ v3_pre_topc(A_198,A_197)
      | ~ v2_tdlat_3(A_197)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | ~ r1_tarski(A_198,u1_struct_0(A_197)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1156])).

tff(c_1193,plain,(
    ! [A_197,A_1] :
      ( u1_struct_0(A_197) = A_1
      | k1_xboole_0 = A_1
      | ~ v3_pre_topc(A_1,A_197)
      | ~ v2_tdlat_3(A_197)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | k4_xboole_0(A_1,u1_struct_0(A_197)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1177])).

tff(c_1280,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_5')
    | '#skF_1'('#skF_4','#skF_5') = k1_xboole_0
    | ~ v3_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_1193])).

tff(c_1296,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_5')
    | '#skF_1'('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_60,c_917,c_1280])).

tff(c_1297,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_1296])).

tff(c_78,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_78])).

tff(c_86,plain,(
    k4_xboole_0('#skF_5',u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_6])).

tff(c_1312,plain,(
    k4_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_86])).

tff(c_1315,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_1312])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1466,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_2])).

tff(c_1468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1466])).

tff(c_1469,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_1516,plain,(
    ! [A_216,B_217] :
      ( '#skF_2'(A_216,B_217) != B_217
      | v3_tex_2(B_217,A_216)
      | ~ v2_tex_2(B_217,A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1526,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1516])).

tff(c_1531,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1526])).

tff(c_1532,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1531])).

tff(c_1533,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1532])).

tff(c_2005,plain,(
    ! [B_275,A_276] :
      ( v2_tex_2(B_275,A_276)
      | ~ v1_zfmisc_1(B_275)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_276)))
      | v1_xboole_0(B_275)
      | ~ l1_pre_topc(A_276)
      | ~ v2_tdlat_3(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2018,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2005])).

tff(c_2024,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_73,c_2018])).

tff(c_2026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_1533,c_2024])).

tff(c_2028,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1532])).

tff(c_2508,plain,(
    ! [B_334,A_335] :
      ( v3_tex_2(B_334,A_335)
      | ~ v2_tex_2(B_334,A_335)
      | ~ v1_tops_1(B_334,A_335)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335)
      | v2_struct_0(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2521,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2508])).

tff(c_2527,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1469,c_2028,c_2521])).

tff(c_2529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_75,c_2527])).

tff(c_2531,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2530,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2586,plain,(
    ! [B_354,A_355] :
      ( v2_tex_2(B_354,A_355)
      | ~ v3_tex_2(B_354,A_355)
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_pre_topc(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2596,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2586])).

tff(c_2601,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2530,c_2596])).

tff(c_3075,plain,(
    ! [B_420,A_421] :
      ( v1_zfmisc_1(B_420)
      | ~ v2_tex_2(B_420,A_421)
      | ~ m1_subset_1(B_420,k1_zfmisc_1(u1_struct_0(A_421)))
      | v1_xboole_0(B_420)
      | ~ l1_pre_topc(A_421)
      | ~ v2_tdlat_3(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3088,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3075])).

tff(c_3094,plain,
    ( v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2601,c_3088])).

tff(c_3096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_2531,c_3094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.73/1.90  
% 4.73/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.73/1.90  %$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.73/1.90  
% 4.73/1.90  %Foreground sorts:
% 4.73/1.90  
% 4.73/1.90  
% 4.73/1.90  %Background operators:
% 4.73/1.90  
% 4.73/1.90  
% 4.73/1.90  %Foreground operators:
% 4.73/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.73/1.90  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.73/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.73/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.73/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.73/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.73/1.90  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.73/1.90  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.73/1.90  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.73/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.73/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.73/1.90  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.73/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.73/1.90  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.73/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.73/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.73/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.73/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.73/1.90  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.73/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.90  
% 5.06/1.92  tff(f_149, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 5.06/1.92  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(C = k1_xboole_0) & v3_pre_topc(C, A)) & r1_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tops_1)).
% 5.06/1.92  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.06/1.92  tff(f_113, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.06/1.92  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 5.06/1.92  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.06/1.92  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.06/1.92  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.06/1.92  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v2_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(B, A) & ~(B = k1_xboole_0)) & ~(B = u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tdlat_3)).
% 5.06/1.92  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.06/1.92  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_72, plain, (v3_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_73, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 5.06/1.92  tff(c_66, plain, (~v1_zfmisc_1('#skF_5') | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_75, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_66])).
% 5.06/1.92  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_177, plain, (![A_62, B_63]: (v3_pre_topc('#skF_1'(A_62, B_63), A_62) | v1_tops_1(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.06/1.92  tff(c_184, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_177])).
% 5.06/1.92  tff(c_189, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_184])).
% 5.06/1.92  tff(c_190, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_189])).
% 5.06/1.92  tff(c_203, plain, (![A_67, B_68]: ('#skF_2'(A_67, B_68)!=B_68 | v3_tex_2(B_68, A_67) | ~v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.06/1.92  tff(c_213, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_203])).
% 5.06/1.92  tff(c_218, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_213])).
% 5.06/1.92  tff(c_219, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_75, c_218])).
% 5.06/1.92  tff(c_220, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_219])).
% 5.06/1.92  tff(c_60, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.06/1.92  tff(c_696, plain, (![B_126, A_127]: (v2_tex_2(B_126, A_127) | ~v1_zfmisc_1(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | v1_xboole_0(B_126) | ~l1_pre_topc(A_127) | ~v2_tdlat_3(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.06/1.92  tff(c_712, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_696])).
% 5.06/1.92  tff(c_719, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_73, c_712])).
% 5.06/1.92  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_220, c_719])).
% 5.06/1.92  tff(c_723, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_219])).
% 5.06/1.92  tff(c_895, plain, (![B_155, A_156]: (v3_tex_2(B_155, A_156) | ~v2_tex_2(B_155, A_156) | ~v1_tops_1(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.06/1.92  tff(c_908, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_895])).
% 5.06/1.92  tff(c_914, plain, (v3_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_190, c_723, c_908])).
% 5.06/1.92  tff(c_916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_75, c_914])).
% 5.06/1.92  tff(c_918, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_189])).
% 5.06/1.92  tff(c_949, plain, (![B_162, A_163]: (r1_xboole_0(B_162, '#skF_1'(A_163, B_162)) | v1_tops_1(B_162, A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.06/1.92  tff(c_956, plain, (r1_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5')) | v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_949])).
% 5.06/1.92  tff(c_961, plain, (r1_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5')) | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_956])).
% 5.06/1.92  tff(c_962, plain, (r1_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_918, c_961])).
% 5.06/1.92  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.06/1.92  tff(c_966, plain, (k4_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_962, c_8])).
% 5.06/1.92  tff(c_144, plain, (![A_58, B_59]: ('#skF_1'(A_58, B_59)!=k1_xboole_0 | v1_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.06/1.92  tff(c_154, plain, ('#skF_1'('#skF_4', '#skF_5')!=k1_xboole_0 | v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_144])).
% 5.06/1.92  tff(c_159, plain, ('#skF_1'('#skF_4', '#skF_5')!=k1_xboole_0 | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_154])).
% 5.06/1.92  tff(c_160, plain, ('#skF_1'('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_159])).
% 5.06/1.92  tff(c_917, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_189])).
% 5.06/1.92  tff(c_1087, plain, (![A_187, B_188]: (m1_subset_1('#skF_1'(A_187, B_188), k1_zfmisc_1(u1_struct_0(A_187))) | v1_tops_1(B_188, A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.06/1.92  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.06/1.92  tff(c_1128, plain, (![A_191, B_192]: (r1_tarski('#skF_1'(A_191, B_192), u1_struct_0(A_191)) | v1_tops_1(B_192, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191))), inference(resolution, [status(thm)], [c_1087, c_12])).
% 5.06/1.92  tff(c_6, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.06/1.92  tff(c_1260, plain, (![A_207, B_208]: (k4_xboole_0('#skF_1'(A_207, B_208), u1_struct_0(A_207))=k1_xboole_0 | v1_tops_1(B_208, A_207) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207))), inference(resolution, [status(thm)], [c_1128, c_6])).
% 5.06/1.92  tff(c_1269, plain, (k4_xboole_0('#skF_1'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))=k1_xboole_0 | v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1260])).
% 5.06/1.92  tff(c_1275, plain, (k4_xboole_0('#skF_1'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))=k1_xboole_0 | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1269])).
% 5.06/1.92  tff(c_1276, plain, (k4_xboole_0('#skF_1'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_918, c_1275])).
% 5.06/1.92  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.06/1.92  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.06/1.92  tff(c_1156, plain, (![A_195, B_196]: (u1_struct_0(A_195)=B_196 | k1_xboole_0=B_196 | ~v3_pre_topc(B_196, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~v2_tdlat_3(A_195) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.06/1.92  tff(c_1177, plain, (![A_197, A_198]: (u1_struct_0(A_197)=A_198 | k1_xboole_0=A_198 | ~v3_pre_topc(A_198, A_197) | ~v2_tdlat_3(A_197) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | ~r1_tarski(A_198, u1_struct_0(A_197)))), inference(resolution, [status(thm)], [c_14, c_1156])).
% 5.06/1.92  tff(c_1193, plain, (![A_197, A_1]: (u1_struct_0(A_197)=A_1 | k1_xboole_0=A_1 | ~v3_pre_topc(A_1, A_197) | ~v2_tdlat_3(A_197) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | k4_xboole_0(A_1, u1_struct_0(A_197))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1177])).
% 5.06/1.92  tff(c_1280, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_5') | '#skF_1'('#skF_4', '#skF_5')=k1_xboole_0 | ~v3_pre_topc('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1276, c_1193])).
% 5.06/1.92  tff(c_1296, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_5') | '#skF_1'('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_60, c_917, c_1280])).
% 5.06/1.92  tff(c_1297, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_160, c_1296])).
% 5.06/1.92  tff(c_78, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.06/1.92  tff(c_82, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_78])).
% 5.06/1.92  tff(c_86, plain, (k4_xboole_0('#skF_5', u1_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_6])).
% 5.06/1.92  tff(c_1312, plain, (k4_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_86])).
% 5.06/1.92  tff(c_1315, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_966, c_1312])).
% 5.06/1.92  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.06/1.92  tff(c_1466, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1315, c_2])).
% 5.06/1.92  tff(c_1468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1466])).
% 5.06/1.92  tff(c_1469, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_159])).
% 5.06/1.92  tff(c_1516, plain, (![A_216, B_217]: ('#skF_2'(A_216, B_217)!=B_217 | v3_tex_2(B_217, A_216) | ~v2_tex_2(B_217, A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.06/1.92  tff(c_1526, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1516])).
% 5.06/1.92  tff(c_1531, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1526])).
% 5.06/1.92  tff(c_1532, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_75, c_1531])).
% 5.06/1.92  tff(c_1533, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1532])).
% 5.06/1.92  tff(c_2005, plain, (![B_275, A_276]: (v2_tex_2(B_275, A_276) | ~v1_zfmisc_1(B_275) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_276))) | v1_xboole_0(B_275) | ~l1_pre_topc(A_276) | ~v2_tdlat_3(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.06/1.92  tff(c_2018, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2005])).
% 5.06/1.92  tff(c_2024, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_73, c_2018])).
% 5.06/1.92  tff(c_2026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_1533, c_2024])).
% 5.06/1.92  tff(c_2028, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1532])).
% 5.06/1.92  tff(c_2508, plain, (![B_334, A_335]: (v3_tex_2(B_334, A_335) | ~v2_tex_2(B_334, A_335) | ~v1_tops_1(B_334, A_335) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_335))) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335) | v2_struct_0(A_335))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.06/1.92  tff(c_2521, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2508])).
% 5.06/1.92  tff(c_2527, plain, (v3_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1469, c_2028, c_2521])).
% 5.06/1.92  tff(c_2529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_75, c_2527])).
% 5.06/1.92  tff(c_2531, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 5.06/1.92  tff(c_2530, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 5.06/1.92  tff(c_2586, plain, (![B_354, A_355]: (v2_tex_2(B_354, A_355) | ~v3_tex_2(B_354, A_355) | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(A_355))) | ~l1_pre_topc(A_355))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.06/1.92  tff(c_2596, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2586])).
% 5.06/1.92  tff(c_2601, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2530, c_2596])).
% 5.06/1.92  tff(c_3075, plain, (![B_420, A_421]: (v1_zfmisc_1(B_420) | ~v2_tex_2(B_420, A_421) | ~m1_subset_1(B_420, k1_zfmisc_1(u1_struct_0(A_421))) | v1_xboole_0(B_420) | ~l1_pre_topc(A_421) | ~v2_tdlat_3(A_421) | ~v2_pre_topc(A_421) | v2_struct_0(A_421))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.06/1.92  tff(c_3088, plain, (v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_3075])).
% 5.06/1.92  tff(c_3094, plain, (v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2601, c_3088])).
% 5.06/1.92  tff(c_3096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_2531, c_3094])).
% 5.06/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.92  
% 5.06/1.92  Inference rules
% 5.06/1.92  ----------------------
% 5.06/1.92  #Ref     : 0
% 5.06/1.92  #Sup     : 637
% 5.06/1.92  #Fact    : 0
% 5.06/1.92  #Define  : 0
% 5.06/1.92  #Split   : 14
% 5.06/1.92  #Chain   : 0
% 5.06/1.92  #Close   : 0
% 5.06/1.92  
% 5.06/1.92  Ordering : KBO
% 5.06/1.92  
% 5.06/1.92  Simplification rules
% 5.06/1.92  ----------------------
% 5.06/1.92  #Subsume      : 82
% 5.06/1.92  #Demod        : 459
% 5.06/1.92  #Tautology    : 148
% 5.06/1.92  #SimpNegUnit  : 59
% 5.06/1.92  #BackRed      : 22
% 5.06/1.92  
% 5.06/1.92  #Partial instantiations: 0
% 5.06/1.92  #Strategies tried      : 1
% 5.06/1.92  
% 5.06/1.92  Timing (in seconds)
% 5.06/1.92  ----------------------
% 5.06/1.92  Preprocessing        : 0.34
% 5.06/1.92  Parsing              : 0.18
% 5.06/1.92  CNF conversion       : 0.02
% 5.06/1.92  Main loop            : 0.78
% 5.06/1.92  Inferencing          : 0.30
% 5.06/1.92  Reduction            : 0.22
% 5.06/1.92  Demodulation         : 0.15
% 5.06/1.92  BG Simplification    : 0.04
% 5.06/1.92  Subsumption          : 0.13
% 5.06/1.92  Abstraction          : 0.04
% 5.06/1.92  MUC search           : 0.00
% 5.06/1.92  Cooper               : 0.00
% 5.06/1.92  Total                : 1.16
% 5.06/1.92  Index Insertion      : 0.00
% 5.06/1.92  Index Deletion       : 0.00
% 5.06/1.92  Index Matching       : 0.00
% 5.06/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
