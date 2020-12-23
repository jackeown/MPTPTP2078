%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:09 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 305 expanded)
%              Number of leaves         :   40 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  203 ( 802 expanded)
%              Number of equality atoms :   53 ( 152 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_28,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_34,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k2_tops_1(A,B)) = k2_tops_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_70,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ r1_tarski(A_49,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [A_56,B_57,C_58] :
      ( k7_subset_1(A_56,B_57,C_58) = k4_xboole_0(B_57,C_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [A_8,C_58] : k7_subset_1(A_8,k1_xboole_0,C_58) = k4_xboole_0(k1_xboole_0,C_58) ),
    inference(resolution,[status(thm)],[c_12,c_111])).

tff(c_118,plain,(
    ! [A_8,C_58] : k7_subset_1(A_8,k1_xboole_0,C_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_115])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_202,plain,(
    ! [B_74,A_75] :
      ( v4_pre_topc(B_74,A_75)
      | ~ v1_xboole_0(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_212,plain,(
    ! [A_75] :
      ( v4_pre_topc(k1_xboole_0,A_75)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_12,c_202])).

tff(c_219,plain,(
    ! [A_75] :
      ( v4_pre_topc(k1_xboole_0,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_212])).

tff(c_3259,plain,(
    ! [A_215,B_216] :
      ( k7_subset_1(u1_struct_0(A_215),B_216,k1_tops_1(A_215,B_216)) = k2_tops_1(A_215,B_216)
      | ~ v4_pre_topc(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3268,plain,(
    ! [A_215] :
      ( k7_subset_1(u1_struct_0(A_215),k1_xboole_0,k1_tops_1(A_215,k1_xboole_0)) = k2_tops_1(A_215,k1_xboole_0)
      | ~ v4_pre_topc(k1_xboole_0,A_215)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215) ) ),
    inference(resolution,[status(thm)],[c_12,c_3259])).

tff(c_3279,plain,(
    ! [A_217] :
      ( k2_tops_1(A_217,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_217)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_3268])).

tff(c_3597,plain,(
    ! [A_231] :
      ( k2_tops_1(A_231,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231) ) ),
    inference(resolution,[status(thm)],[c_219,c_3279])).

tff(c_3600,plain,
    ( k2_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3597])).

tff(c_3603,plain,(
    k2_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3600])).

tff(c_278,plain,(
    ! [A_85,B_86] :
      ( k2_pre_topc(A_85,k2_tops_1(A_85,B_86)) = k2_tops_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_290,plain,(
    ! [A_85] :
      ( k2_pre_topc(A_85,k2_tops_1(A_85,k1_xboole_0)) = k2_tops_1(A_85,k1_xboole_0)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_278])).

tff(c_3635,plain,
    ( k2_tops_1('#skF_1',k1_xboole_0) = k2_pre_topc('#skF_1',k1_xboole_0)
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3603,c_290])).

tff(c_3639,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3603,c_3635])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_222,plain,(
    ! [A_77,B_78] :
      ( v2_tops_1(k2_pre_topc(A_77,B_78),A_77)
      | ~ v3_tops_1(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_226,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_222])).

tff(c_233,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_226])).

tff(c_166,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k2_pre_topc(A_69,B_70),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [A_37,B_39] :
      ( k1_tops_1(A_37,B_39) = k1_xboole_0
      | ~ v2_tops_1(B_39,A_37)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3558,plain,(
    ! [A_229,B_230] :
      ( k1_tops_1(A_229,k2_pre_topc(A_229,B_230)) = k1_xboole_0
      | ~ v2_tops_1(k2_pre_topc(A_229,B_230),A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(resolution,[status(thm)],[c_166,c_40])).

tff(c_3574,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_233,c_3558])).

tff(c_3589,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3574])).

tff(c_48,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3196,plain,(
    ! [A_212,B_213] :
      ( k2_pre_topc(A_212,k1_tops_1(A_212,k2_pre_topc(A_212,B_213))) = k2_pre_topc(A_212,B_213)
      | ~ v3_pre_topc(B_213,A_212)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3202,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3196])).

tff(c_3212,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_3202])).

tff(c_20,plain,(
    ! [B_19,A_17] :
      ( v3_tops_1(B_19,A_17)
      | ~ v2_tops_1(k2_pre_topc(A_17,B_19),A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3224,plain,
    ( v3_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3212,c_20])).

tff(c_3237,plain,
    ( v3_tops_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_233,c_3224])).

tff(c_3284,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3237])).

tff(c_3590,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3589,c_3284])).

tff(c_3594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3590])).

tff(c_3596,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3237])).

tff(c_3787,plain,(
    ! [A_236,B_237] :
      ( k1_tops_1(A_236,k2_pre_topc(A_236,B_237)) = k1_xboole_0
      | ~ v2_tops_1(k2_pre_topc(A_236,B_237),A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(resolution,[status(thm)],[c_166,c_40])).

tff(c_3793,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k1_xboole_0
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3212,c_3787])).

tff(c_3805,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3596,c_233,c_3212,c_3793])).

tff(c_3818,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3805,c_3212])).

tff(c_3822,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3639,c_3818])).

tff(c_136,plain,(
    ! [B_63,A_64] :
      ( v2_tops_1(B_63,A_64)
      | ~ v3_tops_1(B_63,A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_139,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_136])).

tff(c_146,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_139])).

tff(c_149,plain,(
    ! [A_66,B_67] :
      ( k1_tops_1(A_66,B_67) = k1_xboole_0
      | ~ v2_tops_1(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_152,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_149])).

tff(c_159,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_146,c_152])).

tff(c_346,plain,(
    ! [A_93,B_94] :
      ( k7_subset_1(u1_struct_0(A_93),k2_pre_topc(A_93,B_94),k1_tops_1(A_93,B_94)) = k2_tops_1(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_367,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_346])).

tff(c_375,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_367])).

tff(c_3837,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k1_xboole_0,k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3822,c_375])).

tff(c_3840,plain,(
    k2_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_3837])).

tff(c_116,plain,(
    ! [C_58] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_58) = k4_xboole_0('#skF_2',C_58) ),
    inference(resolution,[status(thm)],[c_50,c_111])).

tff(c_325,plain,(
    ! [A_91,B_92] :
      ( k7_subset_1(u1_struct_0(A_91),B_92,k2_tops_1(A_91,B_92)) = k1_tops_1(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_329,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_325])).

tff(c_336,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_159,c_116,c_329])).

tff(c_3881,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3840,c_336])).

tff(c_3890,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3881])).

tff(c_3892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.48/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.08  
% 5.48/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.08  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.48/2.08  
% 5.48/2.08  %Foreground sorts:
% 5.48/2.08  
% 5.48/2.08  
% 5.48/2.08  %Background operators:
% 5.48/2.08  
% 5.48/2.08  
% 5.48/2.08  %Foreground operators:
% 5.48/2.08  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.48/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.48/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.48/2.08  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.48/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.48/2.08  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.48/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.48/2.08  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 5.48/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.48/2.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.48/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.48/2.08  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.48/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.48/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.48/2.08  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.48/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.48/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.48/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.48/2.08  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.48/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.48/2.08  
% 5.48/2.10  tff(f_153, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 5.48/2.10  tff(f_30, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.48/2.10  tff(f_28, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.48/2.10  tff(f_34, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.48/2.10  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.48/2.10  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.48/2.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.48/2.10  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 5.48/2.10  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.48/2.10  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k2_tops_1(A, B)) = k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l79_tops_1)).
% 5.48/2.10  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 5.48/2.10  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.48/2.10  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.48/2.10  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tops_1)).
% 5.48/2.10  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 5.48/2.10  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.48/2.10  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.48/2.10  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.48/2.10  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.48/2.10  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.48/2.10  tff(c_70, plain, (![A_49]: (k1_xboole_0=A_49 | ~r1_tarski(A_49, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.48/2.10  tff(c_81, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_70])).
% 5.48/2.10  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.48/2.10  tff(c_111, plain, (![A_56, B_57, C_58]: (k7_subset_1(A_56, B_57, C_58)=k4_xboole_0(B_57, C_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.48/2.10  tff(c_115, plain, (![A_8, C_58]: (k7_subset_1(A_8, k1_xboole_0, C_58)=k4_xboole_0(k1_xboole_0, C_58))), inference(resolution, [status(thm)], [c_12, c_111])).
% 5.48/2.10  tff(c_118, plain, (![A_8, C_58]: (k7_subset_1(A_8, k1_xboole_0, C_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_115])).
% 5.48/2.10  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.48/2.10  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.48/2.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.48/2.10  tff(c_202, plain, (![B_74, A_75]: (v4_pre_topc(B_74, A_75) | ~v1_xboole_0(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.48/2.10  tff(c_212, plain, (![A_75]: (v4_pre_topc(k1_xboole_0, A_75) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(resolution, [status(thm)], [c_12, c_202])).
% 5.48/2.10  tff(c_219, plain, (![A_75]: (v4_pre_topc(k1_xboole_0, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_212])).
% 5.48/2.10  tff(c_3259, plain, (![A_215, B_216]: (k7_subset_1(u1_struct_0(A_215), B_216, k1_tops_1(A_215, B_216))=k2_tops_1(A_215, B_216) | ~v4_pre_topc(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.48/2.10  tff(c_3268, plain, (![A_215]: (k7_subset_1(u1_struct_0(A_215), k1_xboole_0, k1_tops_1(A_215, k1_xboole_0))=k2_tops_1(A_215, k1_xboole_0) | ~v4_pre_topc(k1_xboole_0, A_215) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215))), inference(resolution, [status(thm)], [c_12, c_3259])).
% 5.48/2.10  tff(c_3279, plain, (![A_217]: (k2_tops_1(A_217, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_217) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_3268])).
% 5.48/2.10  tff(c_3597, plain, (![A_231]: (k2_tops_1(A_231, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231))), inference(resolution, [status(thm)], [c_219, c_3279])).
% 5.48/2.10  tff(c_3600, plain, (k2_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_3597])).
% 5.48/2.10  tff(c_3603, plain, (k2_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3600])).
% 5.48/2.10  tff(c_278, plain, (![A_85, B_86]: (k2_pre_topc(A_85, k2_tops_1(A_85, B_86))=k2_tops_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.48/2.10  tff(c_290, plain, (![A_85]: (k2_pre_topc(A_85, k2_tops_1(A_85, k1_xboole_0))=k2_tops_1(A_85, k1_xboole_0) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(resolution, [status(thm)], [c_12, c_278])).
% 5.48/2.10  tff(c_3635, plain, (k2_tops_1('#skF_1', k1_xboole_0)=k2_pre_topc('#skF_1', k1_xboole_0) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3603, c_290])).
% 5.48/2.10  tff(c_3639, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3603, c_3635])).
% 5.48/2.10  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.48/2.10  tff(c_46, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.48/2.10  tff(c_222, plain, (![A_77, B_78]: (v2_tops_1(k2_pre_topc(A_77, B_78), A_77) | ~v3_tops_1(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.48/2.10  tff(c_226, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_222])).
% 5.48/2.10  tff(c_233, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_226])).
% 5.48/2.10  tff(c_166, plain, (![A_69, B_70]: (m1_subset_1(k2_pre_topc(A_69, B_70), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.48/2.10  tff(c_40, plain, (![A_37, B_39]: (k1_tops_1(A_37, B_39)=k1_xboole_0 | ~v2_tops_1(B_39, A_37) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.48/2.10  tff(c_3558, plain, (![A_229, B_230]: (k1_tops_1(A_229, k2_pre_topc(A_229, B_230))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc(A_229, B_230), A_229) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(resolution, [status(thm)], [c_166, c_40])).
% 5.48/2.10  tff(c_3574, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0 | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_233, c_3558])).
% 5.48/2.10  tff(c_3589, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3574])).
% 5.48/2.10  tff(c_48, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.48/2.10  tff(c_3196, plain, (![A_212, B_213]: (k2_pre_topc(A_212, k1_tops_1(A_212, k2_pre_topc(A_212, B_213)))=k2_pre_topc(A_212, B_213) | ~v3_pre_topc(B_213, A_212) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.48/2.10  tff(c_3202, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3196])).
% 5.48/2.10  tff(c_3212, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_3202])).
% 5.48/2.10  tff(c_20, plain, (![B_19, A_17]: (v3_tops_1(B_19, A_17) | ~v2_tops_1(k2_pre_topc(A_17, B_19), A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.48/2.10  tff(c_3224, plain, (v3_tops_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3212, c_20])).
% 5.48/2.10  tff(c_3237, plain, (v3_tops_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_233, c_3224])).
% 5.48/2.10  tff(c_3284, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_3237])).
% 5.48/2.10  tff(c_3590, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3589, c_3284])).
% 5.48/2.10  tff(c_3594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3590])).
% 5.48/2.10  tff(c_3596, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_3237])).
% 5.48/2.10  tff(c_3787, plain, (![A_236, B_237]: (k1_tops_1(A_236, k2_pre_topc(A_236, B_237))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc(A_236, B_237), A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(resolution, [status(thm)], [c_166, c_40])).
% 5.48/2.10  tff(c_3793, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3212, c_3787])).
% 5.48/2.10  tff(c_3805, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3596, c_233, c_3212, c_3793])).
% 5.48/2.10  tff(c_3818, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3805, c_3212])).
% 5.48/2.10  tff(c_3822, plain, (k2_pre_topc('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3639, c_3818])).
% 5.48/2.10  tff(c_136, plain, (![B_63, A_64]: (v2_tops_1(B_63, A_64) | ~v3_tops_1(B_63, A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.48/2.10  tff(c_139, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_136])).
% 5.48/2.10  tff(c_146, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_139])).
% 5.48/2.10  tff(c_149, plain, (![A_66, B_67]: (k1_tops_1(A_66, B_67)=k1_xboole_0 | ~v2_tops_1(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.48/2.10  tff(c_152, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_149])).
% 5.48/2.10  tff(c_159, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_146, c_152])).
% 5.48/2.10  tff(c_346, plain, (![A_93, B_94]: (k7_subset_1(u1_struct_0(A_93), k2_pre_topc(A_93, B_94), k1_tops_1(A_93, B_94))=k2_tops_1(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.48/2.10  tff(c_367, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_159, c_346])).
% 5.48/2.10  tff(c_375, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_367])).
% 5.48/2.10  tff(c_3837, plain, (k7_subset_1(u1_struct_0('#skF_1'), k1_xboole_0, k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3822, c_375])).
% 5.48/2.10  tff(c_3840, plain, (k2_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_118, c_3837])).
% 5.48/2.10  tff(c_116, plain, (![C_58]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_58)=k4_xboole_0('#skF_2', C_58))), inference(resolution, [status(thm)], [c_50, c_111])).
% 5.48/2.10  tff(c_325, plain, (![A_91, B_92]: (k7_subset_1(u1_struct_0(A_91), B_92, k2_tops_1(A_91, B_92))=k1_tops_1(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.48/2.10  tff(c_329, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_325])).
% 5.48/2.10  tff(c_336, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_159, c_116, c_329])).
% 5.48/2.10  tff(c_3881, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3840, c_336])).
% 5.48/2.10  tff(c_3890, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3881])).
% 5.48/2.10  tff(c_3892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_3890])).
% 5.48/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.10  
% 5.48/2.10  Inference rules
% 5.48/2.10  ----------------------
% 5.48/2.10  #Ref     : 0
% 5.48/2.10  #Sup     : 823
% 5.48/2.10  #Fact    : 0
% 5.48/2.10  #Define  : 0
% 5.48/2.10  #Split   : 55
% 5.48/2.10  #Chain   : 0
% 5.48/2.10  #Close   : 0
% 5.48/2.10  
% 5.48/2.10  Ordering : KBO
% 5.48/2.10  
% 5.48/2.10  Simplification rules
% 5.48/2.10  ----------------------
% 5.48/2.10  #Subsume      : 102
% 5.48/2.10  #Demod        : 1493
% 5.48/2.10  #Tautology    : 372
% 5.48/2.10  #SimpNegUnit  : 57
% 5.48/2.10  #BackRed      : 94
% 5.48/2.10  
% 5.48/2.10  #Partial instantiations: 0
% 5.48/2.10  #Strategies tried      : 1
% 5.48/2.10  
% 5.48/2.10  Timing (in seconds)
% 5.48/2.10  ----------------------
% 5.48/2.10  Preprocessing        : 0.33
% 5.48/2.10  Parsing              : 0.18
% 5.48/2.10  CNF conversion       : 0.02
% 5.48/2.10  Main loop            : 0.98
% 5.48/2.10  Inferencing          : 0.31
% 5.48/2.10  Reduction            : 0.38
% 5.48/2.10  Demodulation         : 0.27
% 5.48/2.10  BG Simplification    : 0.04
% 5.48/2.10  Subsumption          : 0.17
% 5.48/2.10  Abstraction          : 0.04
% 5.48/2.10  MUC search           : 0.00
% 5.48/2.10  Cooper               : 0.00
% 5.48/2.10  Total                : 1.35
% 5.48/2.10  Index Insertion      : 0.00
% 5.48/2.10  Index Deletion       : 0.00
% 5.48/2.10  Index Matching       : 0.00
% 5.48/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
