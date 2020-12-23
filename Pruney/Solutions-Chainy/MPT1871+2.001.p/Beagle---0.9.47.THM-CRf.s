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
% DateTime   : Thu Dec  3 10:29:36 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   99 (1324 expanded)
%              Number of leaves         :   24 ( 517 expanded)
%              Depth                    :   17
%              Number of atoms          :  406 (6938 expanded)
%              Number of equality atoms :   16 ( 283 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A)
                    & v2_tex_2(B,A)
                    & v2_tex_2(C,A) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tex_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => ( v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A)
                    & v4_pre_topc(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A)
                    & v2_tex_2(B,A)
                    & v2_tex_2(C,A) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tex_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_37,plain,(
    ! [A_29,B_30,C_31] :
      ( k4_subset_1(A_29,B_30,C_31) = k2_xboole_0(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [B_32] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_32,'#skF_5') = k2_xboole_0(B_32,'#skF_5')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_52,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_18,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_57,plain,(
    ~ v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_26,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    v4_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_22,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_20,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_117,plain,(
    ! [A_42,B_43,C_44] :
      ( v4_pre_topc('#skF_1'(A_42),A_42)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_42),B_43,C_44),A_42)
      | ~ v2_tex_2(C_44,A_42)
      | ~ v2_tex_2(B_43,A_42)
      | ~ v4_pre_topc(C_44,A_42)
      | ~ v4_pre_topc(B_43,A_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_126,plain,
    ( v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_117])).

tff(c_135,plain,
    ( v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_20,c_126])).

tff(c_136,plain,(
    v4_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_135])).

tff(c_16,plain,(
    ! [A_14,B_22,C_24] :
      ( m1_subset_1('#skF_1'(A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_14),B_22,C_24),A_14)
      | ~ v2_tex_2(C_24,A_14)
      | ~ v2_tex_2(B_22,A_14)
      | ~ v4_pre_topc(C_24,A_14)
      | ~ v4_pre_topc(B_22,A_14)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_166,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1('#skF_1'(A_48),k1_zfmisc_1(u1_struct_0(A_48)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_48),B_49,C_50),A_48)
      | ~ v2_tex_2(C_50,A_48)
      | ~ v2_tex_2(B_49,A_48)
      | ~ v4_pre_topc(C_50,A_48)
      | ~ v4_pre_topc(B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [B_30] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_30,'#skF_5') = k2_xboole_0(B_30,'#skF_5')
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_184,plain,(
    ! [B_49,C_50] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_5') = k2_xboole_0('#skF_1'('#skF_3'),'#skF_5')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_49,C_50),'#skF_3')
      | ~ v2_tex_2(C_50,'#skF_3')
      | ~ v2_tex_2(B_49,'#skF_3')
      | ~ v4_pre_topc(C_50,'#skF_3')
      | ~ v4_pre_topc(B_49,'#skF_3')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_166,c_42])).

tff(c_203,plain,(
    ! [B_49,C_50] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_5') = k2_xboole_0('#skF_1'('#skF_3'),'#skF_5')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_49,C_50),'#skF_3')
      | ~ v2_tex_2(C_50,'#skF_3')
      | ~ v2_tex_2(B_49,'#skF_3')
      | ~ v4_pre_topc(C_50,'#skF_3')
      | ~ v4_pre_topc(B_49,'#skF_3')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_184])).

tff(c_207,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_5') = k2_xboole_0('#skF_1'('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_228,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1('#skF_2'(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_51),B_52,C_53),A_51)
      | ~ v2_tex_2(C_53,A_51)
      | ~ v2_tex_2(B_52,A_51)
      | ~ v4_pre_topc(C_53,A_51)
      | ~ v4_pre_topc(B_52,A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_251,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2(k2_xboole_0('#skF_1'('#skF_3'),'#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_228])).

tff(c_271,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2(k2_xboole_0('#skF_1'('#skF_3'),'#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_136,c_24,c_20,c_251])).

tff(c_272,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_280,plain,(
    ! [B_22,C_24] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_22,C_24),'#skF_3')
      | ~ v2_tex_2(C_24,'#skF_3')
      | ~ v2_tex_2(B_22,'#skF_3')
      | ~ v4_pre_topc(C_24,'#skF_3')
      | ~ v4_pre_topc(B_22,'#skF_3')
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_272])).

tff(c_284,plain,(
    ! [B_57,C_58] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_57,C_58),'#skF_3')
      | ~ v2_tex_2(C_58,'#skF_3')
      | ~ v2_tex_2(B_57,'#skF_3')
      | ~ v4_pre_topc(C_58,'#skF_3')
      | ~ v4_pre_topc(B_57,'#skF_3')
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_280])).

tff(c_296,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_284])).

tff(c_307,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_296])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_307])).

tff(c_311,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_142,plain,(
    ! [A_45,B_46,C_47] :
      ( v4_pre_topc('#skF_2'(A_45),A_45)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_45),B_46,C_47),A_45)
      | ~ v2_tex_2(C_47,A_45)
      | ~ v2_tex_2(B_46,A_45)
      | ~ v4_pre_topc(C_47,A_45)
      | ~ v4_pre_topc(B_46,A_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_151,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_142])).

tff(c_160,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_20,c_151])).

tff(c_161,plain,(
    v4_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_160])).

tff(c_14,plain,(
    ! [A_14,B_22,C_24] :
      ( m1_subset_1('#skF_2'(A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_14),B_22,C_24),A_14)
      | ~ v2_tex_2(C_24,A_14)
      | ~ v2_tex_2(B_22,A_14)
      | ~ v4_pre_topc(C_24,A_14)
      | ~ v4_pre_topc(B_22,A_14)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_subset_1(A_1,B_2,C_3) = k2_xboole_0(B_2,C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_572,plain,(
    ! [A_68,B_69,B_70,C_71] :
      ( k4_subset_1(u1_struct_0(A_68),B_69,'#skF_2'(A_68)) = k2_xboole_0(B_69,'#skF_2'(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_68),B_70,C_71),A_68)
      | ~ v2_tex_2(C_71,A_68)
      | ~ v2_tex_2(B_70,A_68)
      | ~ v4_pre_topc(C_71,A_68)
      | ~ v4_pre_topc(B_70,A_68)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_228,c_2])).

tff(c_582,plain,(
    ! [B_70,C_71] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_2'('#skF_3')) = k2_xboole_0('#skF_4','#skF_2'('#skF_3'))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_70,C_71),'#skF_3')
      | ~ v2_tex_2(C_71,'#skF_3')
      | ~ v2_tex_2(B_70,'#skF_3')
      | ~ v4_pre_topc(C_71,'#skF_3')
      | ~ v4_pre_topc(B_70,'#skF_3')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_572])).

tff(c_593,plain,(
    ! [B_70,C_71] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_2'('#skF_3')) = k2_xboole_0('#skF_4','#skF_2'('#skF_3'))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_70,C_71),'#skF_3')
      | ~ v2_tex_2(C_71,'#skF_3')
      | ~ v2_tex_2(B_70,'#skF_3')
      | ~ v4_pre_topc(C_71,'#skF_3')
      | ~ v4_pre_topc(B_70,'#skF_3')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_582])).

tff(c_619,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_2'('#skF_3')) = k2_xboole_0('#skF_4','#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_4,plain,(
    ! [B_5,C_6,A_4] :
      ( v4_pre_topc(k2_xboole_0(B_5,C_6),A_4)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v4_pre_topc(C_6,A_4)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v4_pre_topc(B_5,A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_729,plain,(
    ! [B_76,A_77,B_78,C_79] :
      ( v4_pre_topc(k2_xboole_0(B_76,'#skF_2'(A_77)),A_77)
      | ~ v4_pre_topc('#skF_2'(A_77),A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v4_pre_topc(B_76,A_77)
      | ~ v2_pre_topc(A_77)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_77),B_78,C_79),A_77)
      | ~ v2_tex_2(C_79,A_77)
      | ~ v2_tex_2(B_78,A_77)
      | ~ v4_pre_topc(C_79,A_77)
      | ~ v4_pre_topc(B_78,A_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_228,c_4])).

tff(c_735,plain,(
    ! [B_76] :
      ( v4_pre_topc(k2_xboole_0(B_76,'#skF_2'('#skF_3')),'#skF_3')
      | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_76,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_tex_2(k2_xboole_0('#skF_4','#skF_2'('#skF_3')),'#skF_3')
      | ~ v2_tex_2('#skF_2'('#skF_3'),'#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ v4_pre_topc('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_729])).

tff(c_770,plain,(
    ! [B_76] :
      ( v4_pre_topc(k2_xboole_0(B_76,'#skF_2'('#skF_3')),'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_76,'#skF_3')
      | v2_tex_2(k2_xboole_0('#skF_4','#skF_2'('#skF_3')),'#skF_3')
      | ~ v2_tex_2('#skF_2'('#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_161,c_22,c_34,c_161,c_735])).

tff(c_789,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_797,plain,(
    ! [B_22,C_24] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_22,C_24),'#skF_3')
      | ~ v2_tex_2(C_24,'#skF_3')
      | ~ v2_tex_2(B_22,'#skF_3')
      | ~ v4_pre_topc(C_24,'#skF_3')
      | ~ v4_pre_topc(B_22,'#skF_3')
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_789])).

tff(c_801,plain,(
    ! [B_83,C_84] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_83,C_84),'#skF_3')
      | ~ v2_tex_2(C_84,'#skF_3')
      | ~ v2_tex_2(B_83,'#skF_3')
      | ~ v4_pre_topc(C_84,'#skF_3')
      | ~ v4_pre_topc(B_83,'#skF_3')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_797])).

tff(c_843,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_801])).

tff(c_874,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_843])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_874])).

tff(c_878,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_896,plain,(
    ! [B_5] :
      ( v4_pre_topc(k2_xboole_0(B_5,'#skF_2'('#skF_3')),'#skF_3')
      | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_5,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_878,c_4])).

tff(c_920,plain,(
    ! [B_5] :
      ( v4_pre_topc(k2_xboole_0(B_5,'#skF_2'('#skF_3')),'#skF_3')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_5,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_161,c_896])).

tff(c_574,plain,(
    ! [B_70,C_71] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')) = k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3'))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_70,C_71),'#skF_3')
      | ~ v2_tex_2(C_71,'#skF_3')
      | ~ v2_tex_2(B_70,'#skF_3')
      | ~ v4_pre_topc(C_71,'#skF_3')
      | ~ v4_pre_topc(B_70,'#skF_3')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_311,c_572])).

tff(c_585,plain,(
    ! [B_70,C_71] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')) = k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3'))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_70,C_71),'#skF_3')
      | ~ v2_tex_2(C_71,'#skF_3')
      | ~ v2_tex_2(B_70,'#skF_3')
      | ~ v4_pre_topc(C_71,'#skF_3')
      | ~ v4_pre_topc(B_70,'#skF_3')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_574])).

tff(c_644,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')) = k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_6,plain,(
    ! [A_7,B_11,C_13] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_7),B_11,C_13),A_7)
      | ~ v4_pre_topc(C_13,A_7)
      | ~ v4_pre_topc(B_11,A_7)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_465,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(A_61),'#skF_1'(A_61),'#skF_2'(A_61)),A_61)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(A_61),'#skF_1'(A_61),'#skF_2'(A_61)),A_61)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_61),B_62,C_63),A_61)
      | ~ v2_tex_2(C_63,A_61)
      | ~ v2_tex_2(B_62,A_61)
      | ~ v4_pre_topc(C_63,A_61)
      | ~ v4_pre_topc(B_62,A_61)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_996,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(A_87),'#skF_1'(A_87),'#skF_2'(A_87)),A_87)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_87),B_88,C_89),A_87)
      | ~ v2_tex_2(C_89,A_87)
      | ~ v2_tex_2(B_88,A_87)
      | ~ v4_pre_topc(C_89,A_87)
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v4_pre_topc('#skF_2'(A_87),A_87)
      | ~ v4_pre_topc('#skF_1'(A_87),A_87)
      | ~ m1_subset_1('#skF_2'(A_87),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1('#skF_1'(A_87),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_465])).

tff(c_998,plain,(
    ! [B_88,C_89] :
      ( ~ v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_88,C_89),'#skF_3')
      | ~ v2_tex_2(C_89,'#skF_3')
      | ~ v2_tex_2(B_88,'#skF_3')
      | ~ v4_pre_topc(C_89,'#skF_3')
      | ~ v4_pre_topc(B_88,'#skF_3')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_996])).

tff(c_1000,plain,(
    ! [B_88,C_89] :
      ( ~ v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_88,C_89),'#skF_3')
      | ~ v2_tex_2(C_89,'#skF_3')
      | ~ v2_tex_2(B_88,'#skF_3')
      | ~ v4_pre_topc(C_89,'#skF_3')
      | ~ v4_pre_topc(B_88,'#skF_3')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_311,c_878,c_136,c_161,c_998])).

tff(c_1005,plain,(
    ~ v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1009,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_920,c_1005])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_311,c_1009])).

tff(c_1019,plain,(
    ! [B_90,C_91] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_90,C_91),'#skF_3')
      | ~ v2_tex_2(C_91,'#skF_3')
      | ~ v2_tex_2(B_90,'#skF_3')
      | ~ v4_pre_topc(C_91,'#skF_3')
      | ~ v4_pre_topc(B_90,'#skF_3')
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_1064,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1019])).

tff(c_1097,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_1064])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1097])).

tff(c_1102,plain,(
    ! [B_92,C_93] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_92,C_93),'#skF_3')
      | ~ v2_tex_2(C_93,'#skF_3')
      | ~ v2_tex_2(B_92,'#skF_3')
      | ~ v4_pre_topc(C_93,'#skF_3')
      | ~ v4_pre_topc(B_92,'#skF_3')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_1141,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1102])).

tff(c_1170,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_1141])).

tff(c_1172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.56  
% 3.57/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.56  %$ v4_pre_topc > v2_tex_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.57/1.56  
% 3.57/1.56  %Foreground sorts:
% 3.57/1.56  
% 3.57/1.56  
% 3.57/1.56  %Background operators:
% 3.57/1.56  
% 3.57/1.56  
% 3.57/1.56  %Foreground operators:
% 3.57/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.57/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.57/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.57/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.56  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.57/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.56  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.57/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.57/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.57/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.57/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.57/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.56  
% 3.57/1.58  tff(f_117, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((v4_pre_topc(B, A) & v4_pre_topc(C, A)) & v2_tex_2(B, A)) & v2_tex_2(C, A)) => v2_tex_2(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_tex_2)).
% 3.57/1.58  tff(f_31, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.57/1.58  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => ((![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A) & v4_pre_topc(k4_subset_1(u1_struct_0(A), B, C), A))))))) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((v4_pre_topc(B, A) & v4_pre_topc(C, A)) & v2_tex_2(B, A)) & v2_tex_2(C, A)) => v2_tex_2(k4_subset_1(u1_struct_0(A), B, C), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tex_2)).
% 3.57/1.58  tff(f_45, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_tops_1)).
% 3.57/1.58  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 3.57/1.58  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_37, plain, (![A_29, B_30, C_31]: (k4_subset_1(A_29, B_30, C_31)=k2_xboole_0(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.58  tff(c_44, plain, (![B_32]: (k4_subset_1(u1_struct_0('#skF_3'), B_32, '#skF_5')=k2_xboole_0(B_32, '#skF_5') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_28, c_37])).
% 3.57/1.58  tff(c_52, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_44])).
% 3.57/1.58  tff(c_18, plain, (~v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_57, plain, (~v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 3.57/1.58  tff(c_26, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_24, plain, (v4_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_22, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_20, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_117, plain, (![A_42, B_43, C_44]: (v4_pre_topc('#skF_1'(A_42), A_42) | v2_tex_2(k4_subset_1(u1_struct_0(A_42), B_43, C_44), A_42) | ~v2_tex_2(C_44, A_42) | ~v2_tex_2(B_43, A_42) | ~v4_pre_topc(C_44, A_42) | ~v4_pre_topc(B_43, A_42) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.58  tff(c_126, plain, (v4_pre_topc('#skF_1'('#skF_3'), '#skF_3') | v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_52, c_117])).
% 3.57/1.58  tff(c_135, plain, (v4_pre_topc('#skF_1'('#skF_3'), '#skF_3') | v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_22, c_20, c_126])).
% 3.57/1.58  tff(c_136, plain, (v4_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_135])).
% 3.57/1.58  tff(c_16, plain, (![A_14, B_22, C_24]: (m1_subset_1('#skF_1'(A_14), k1_zfmisc_1(u1_struct_0(A_14))) | v2_tex_2(k4_subset_1(u1_struct_0(A_14), B_22, C_24), A_14) | ~v2_tex_2(C_24, A_14) | ~v2_tex_2(B_22, A_14) | ~v4_pre_topc(C_24, A_14) | ~v4_pre_topc(B_22, A_14) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.58  tff(c_166, plain, (![A_48, B_49, C_50]: (m1_subset_1('#skF_1'(A_48), k1_zfmisc_1(u1_struct_0(A_48))) | v2_tex_2(k4_subset_1(u1_struct_0(A_48), B_49, C_50), A_48) | ~v2_tex_2(C_50, A_48) | ~v2_tex_2(B_49, A_48) | ~v4_pre_topc(C_50, A_48) | ~v4_pre_topc(B_49, A_48) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.58  tff(c_42, plain, (![B_30]: (k4_subset_1(u1_struct_0('#skF_3'), B_30, '#skF_5')=k2_xboole_0(B_30, '#skF_5') | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_28, c_37])).
% 3.57/1.58  tff(c_184, plain, (![B_49, C_50]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'), '#skF_5')=k2_xboole_0('#skF_1'('#skF_3'), '#skF_5') | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_49, C_50), '#skF_3') | ~v2_tex_2(C_50, '#skF_3') | ~v2_tex_2(B_49, '#skF_3') | ~v4_pre_topc(C_50, '#skF_3') | ~v4_pre_topc(B_49, '#skF_3') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_166, c_42])).
% 3.57/1.58  tff(c_203, plain, (![B_49, C_50]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'), '#skF_5')=k2_xboole_0('#skF_1'('#skF_3'), '#skF_5') | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_49, C_50), '#skF_3') | ~v2_tex_2(C_50, '#skF_3') | ~v2_tex_2(B_49, '#skF_3') | ~v4_pre_topc(C_50, '#skF_3') | ~v4_pre_topc(B_49, '#skF_3') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_184])).
% 3.57/1.58  tff(c_207, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'), '#skF_5')=k2_xboole_0('#skF_1'('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_203])).
% 3.57/1.58  tff(c_228, plain, (![A_51, B_52, C_53]: (m1_subset_1('#skF_2'(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | v2_tex_2(k4_subset_1(u1_struct_0(A_51), B_52, C_53), A_51) | ~v2_tex_2(C_53, A_51) | ~v2_tex_2(B_52, A_51) | ~v4_pre_topc(C_53, A_51) | ~v4_pre_topc(B_52, A_51) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.58  tff(c_251, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(k2_xboole_0('#skF_1'('#skF_3'), '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_228])).
% 3.57/1.58  tff(c_271, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(k2_xboole_0('#skF_1'('#skF_3'), '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_136, c_24, c_20, c_251])).
% 3.57/1.58  tff(c_272, plain, (~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_271])).
% 3.57/1.58  tff(c_280, plain, (![B_22, C_24]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_22, C_24), '#skF_3') | ~v2_tex_2(C_24, '#skF_3') | ~v2_tex_2(B_22, '#skF_3') | ~v4_pre_topc(C_24, '#skF_3') | ~v4_pre_topc(B_22, '#skF_3') | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_272])).
% 3.57/1.58  tff(c_284, plain, (![B_57, C_58]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_57, C_58), '#skF_3') | ~v2_tex_2(C_58, '#skF_3') | ~v2_tex_2(B_57, '#skF_3') | ~v4_pre_topc(C_58, '#skF_3') | ~v4_pre_topc(B_57, '#skF_3') | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_280])).
% 3.57/1.58  tff(c_296, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_284])).
% 3.57/1.58  tff(c_307, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_296])).
% 3.57/1.58  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_307])).
% 3.57/1.58  tff(c_311, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_271])).
% 3.57/1.58  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.58  tff(c_142, plain, (![A_45, B_46, C_47]: (v4_pre_topc('#skF_2'(A_45), A_45) | v2_tex_2(k4_subset_1(u1_struct_0(A_45), B_46, C_47), A_45) | ~v2_tex_2(C_47, A_45) | ~v2_tex_2(B_46, A_45) | ~v4_pre_topc(C_47, A_45) | ~v4_pre_topc(B_46, A_45) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.58  tff(c_151, plain, (v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_52, c_142])).
% 3.57/1.58  tff(c_160, plain, (v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_22, c_20, c_151])).
% 3.57/1.58  tff(c_161, plain, (v4_pre_topc('#skF_2'('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_160])).
% 3.57/1.58  tff(c_14, plain, (![A_14, B_22, C_24]: (m1_subset_1('#skF_2'(A_14), k1_zfmisc_1(u1_struct_0(A_14))) | v2_tex_2(k4_subset_1(u1_struct_0(A_14), B_22, C_24), A_14) | ~v2_tex_2(C_24, A_14) | ~v2_tex_2(B_22, A_14) | ~v4_pre_topc(C_24, A_14) | ~v4_pre_topc(B_22, A_14) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.58  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_subset_1(A_1, B_2, C_3)=k2_xboole_0(B_2, C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.58  tff(c_572, plain, (![A_68, B_69, B_70, C_71]: (k4_subset_1(u1_struct_0(A_68), B_69, '#skF_2'(A_68))=k2_xboole_0(B_69, '#skF_2'(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | v2_tex_2(k4_subset_1(u1_struct_0(A_68), B_70, C_71), A_68) | ~v2_tex_2(C_71, A_68) | ~v2_tex_2(B_70, A_68) | ~v4_pre_topc(C_71, A_68) | ~v4_pre_topc(B_70, A_68) | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_228, c_2])).
% 3.57/1.58  tff(c_582, plain, (![B_70, C_71]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_2'('#skF_3'))=k2_xboole_0('#skF_4', '#skF_2'('#skF_3')) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_70, C_71), '#skF_3') | ~v2_tex_2(C_71, '#skF_3') | ~v2_tex_2(B_70, '#skF_3') | ~v4_pre_topc(C_71, '#skF_3') | ~v4_pre_topc(B_70, '#skF_3') | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_572])).
% 3.57/1.58  tff(c_593, plain, (![B_70, C_71]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_2'('#skF_3'))=k2_xboole_0('#skF_4', '#skF_2'('#skF_3')) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_70, C_71), '#skF_3') | ~v2_tex_2(C_71, '#skF_3') | ~v2_tex_2(B_70, '#skF_3') | ~v4_pre_topc(C_71, '#skF_3') | ~v4_pre_topc(B_70, '#skF_3') | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_582])).
% 3.57/1.58  tff(c_619, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_2'('#skF_3'))=k2_xboole_0('#skF_4', '#skF_2'('#skF_3'))), inference(splitLeft, [status(thm)], [c_593])).
% 3.57/1.58  tff(c_4, plain, (![B_5, C_6, A_4]: (v4_pre_topc(k2_xboole_0(B_5, C_6), A_4) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0(A_4))) | ~v4_pre_topc(C_6, A_4) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~v4_pre_topc(B_5, A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.58  tff(c_729, plain, (![B_76, A_77, B_78, C_79]: (v4_pre_topc(k2_xboole_0(B_76, '#skF_2'(A_77)), A_77) | ~v4_pre_topc('#skF_2'(A_77), A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~v4_pre_topc(B_76, A_77) | ~v2_pre_topc(A_77) | v2_tex_2(k4_subset_1(u1_struct_0(A_77), B_78, C_79), A_77) | ~v2_tex_2(C_79, A_77) | ~v2_tex_2(B_78, A_77) | ~v4_pre_topc(C_79, A_77) | ~v4_pre_topc(B_78, A_77) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_228, c_4])).
% 3.57/1.58  tff(c_735, plain, (![B_76]: (v4_pre_topc(k2_xboole_0(B_76, '#skF_2'('#skF_3')), '#skF_3') | ~v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_76, '#skF_3') | ~v2_pre_topc('#skF_3') | v2_tex_2(k2_xboole_0('#skF_4', '#skF_2'('#skF_3')), '#skF_3') | ~v2_tex_2('#skF_2'('#skF_3'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_619, c_729])).
% 3.57/1.58  tff(c_770, plain, (![B_76]: (v4_pre_topc(k2_xboole_0(B_76, '#skF_2'('#skF_3')), '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_76, '#skF_3') | v2_tex_2(k2_xboole_0('#skF_4', '#skF_2'('#skF_3')), '#skF_3') | ~v2_tex_2('#skF_2'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_161, c_22, c_34, c_161, c_735])).
% 3.57/1.58  tff(c_789, plain, (~m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_770])).
% 3.57/1.58  tff(c_797, plain, (![B_22, C_24]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_22, C_24), '#skF_3') | ~v2_tex_2(C_24, '#skF_3') | ~v2_tex_2(B_22, '#skF_3') | ~v4_pre_topc(C_24, '#skF_3') | ~v4_pre_topc(B_22, '#skF_3') | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_789])).
% 3.57/1.58  tff(c_801, plain, (![B_83, C_84]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_83, C_84), '#skF_3') | ~v2_tex_2(C_84, '#skF_3') | ~v2_tex_2(B_83, '#skF_3') | ~v4_pre_topc(C_84, '#skF_3') | ~v4_pre_topc(B_83, '#skF_3') | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_797])).
% 3.57/1.58  tff(c_843, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_801])).
% 3.57/1.58  tff(c_874, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_843])).
% 3.57/1.58  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_874])).
% 3.57/1.58  tff(c_878, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_770])).
% 3.57/1.58  tff(c_896, plain, (![B_5]: (v4_pre_topc(k2_xboole_0(B_5, '#skF_2'('#skF_3')), '#skF_3') | ~v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_5, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_878, c_4])).
% 3.57/1.58  tff(c_920, plain, (![B_5]: (v4_pre_topc(k2_xboole_0(B_5, '#skF_2'('#skF_3')), '#skF_3') | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_161, c_896])).
% 3.57/1.58  tff(c_574, plain, (![B_70, C_71]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'), '#skF_2'('#skF_3'))=k2_xboole_0('#skF_1'('#skF_3'), '#skF_2'('#skF_3')) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_70, C_71), '#skF_3') | ~v2_tex_2(C_71, '#skF_3') | ~v2_tex_2(B_70, '#skF_3') | ~v4_pre_topc(C_71, '#skF_3') | ~v4_pre_topc(B_70, '#skF_3') | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_311, c_572])).
% 3.57/1.58  tff(c_585, plain, (![B_70, C_71]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'), '#skF_2'('#skF_3'))=k2_xboole_0('#skF_1'('#skF_3'), '#skF_2'('#skF_3')) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_70, C_71), '#skF_3') | ~v2_tex_2(C_71, '#skF_3') | ~v2_tex_2(B_70, '#skF_3') | ~v4_pre_topc(C_71, '#skF_3') | ~v4_pre_topc(B_70, '#skF_3') | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_574])).
% 3.57/1.58  tff(c_644, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'), '#skF_2'('#skF_3'))=k2_xboole_0('#skF_1'('#skF_3'), '#skF_2'('#skF_3'))), inference(splitLeft, [status(thm)], [c_585])).
% 3.57/1.58  tff(c_6, plain, (![A_7, B_11, C_13]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_7), B_11, C_13), A_7) | ~v4_pre_topc(C_13, A_7) | ~v4_pre_topc(B_11, A_7) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.57/1.58  tff(c_465, plain, (![A_61, B_62, C_63]: (~v4_pre_topc(k4_subset_1(u1_struct_0(A_61), '#skF_1'(A_61), '#skF_2'(A_61)), A_61) | ~v4_pre_topc(k9_subset_1(u1_struct_0(A_61), '#skF_1'(A_61), '#skF_2'(A_61)), A_61) | v2_tex_2(k4_subset_1(u1_struct_0(A_61), B_62, C_63), A_61) | ~v2_tex_2(C_63, A_61) | ~v2_tex_2(B_62, A_61) | ~v4_pre_topc(C_63, A_61) | ~v4_pre_topc(B_62, A_61) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.58  tff(c_996, plain, (![A_87, B_88, C_89]: (~v4_pre_topc(k4_subset_1(u1_struct_0(A_87), '#skF_1'(A_87), '#skF_2'(A_87)), A_87) | v2_tex_2(k4_subset_1(u1_struct_0(A_87), B_88, C_89), A_87) | ~v2_tex_2(C_89, A_87) | ~v2_tex_2(B_88, A_87) | ~v4_pre_topc(C_89, A_87) | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~v4_pre_topc('#skF_2'(A_87), A_87) | ~v4_pre_topc('#skF_1'(A_87), A_87) | ~m1_subset_1('#skF_2'(A_87), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1('#skF_1'(A_87), k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(resolution, [status(thm)], [c_6, c_465])).
% 3.57/1.58  tff(c_998, plain, (![B_88, C_89]: (~v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'), '#skF_2'('#skF_3')), '#skF_3') | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_88, C_89), '#skF_3') | ~v2_tex_2(C_89, '#skF_3') | ~v2_tex_2(B_88, '#skF_3') | ~v4_pre_topc(C_89, '#skF_3') | ~v4_pre_topc(B_88, '#skF_3') | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~v4_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_644, c_996])).
% 3.57/1.58  tff(c_1000, plain, (![B_88, C_89]: (~v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'), '#skF_2'('#skF_3')), '#skF_3') | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_88, C_89), '#skF_3') | ~v2_tex_2(C_89, '#skF_3') | ~v2_tex_2(B_88, '#skF_3') | ~v4_pre_topc(C_89, '#skF_3') | ~v4_pre_topc(B_88, '#skF_3') | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_311, c_878, c_136, c_161, c_998])).
% 3.57/1.58  tff(c_1005, plain, (~v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'), '#skF_2'('#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_1000])).
% 3.57/1.58  tff(c_1009, plain, (~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_920, c_1005])).
% 3.57/1.58  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_311, c_1009])).
% 3.57/1.58  tff(c_1019, plain, (![B_90, C_91]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_90, C_91), '#skF_3') | ~v2_tex_2(C_91, '#skF_3') | ~v2_tex_2(B_90, '#skF_3') | ~v4_pre_topc(C_91, '#skF_3') | ~v4_pre_topc(B_90, '#skF_3') | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_1000])).
% 3.57/1.58  tff(c_1064, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1019])).
% 3.57/1.58  tff(c_1097, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_1064])).
% 3.57/1.58  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1097])).
% 3.57/1.58  tff(c_1102, plain, (![B_92, C_93]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_92, C_93), '#skF_3') | ~v2_tex_2(C_93, '#skF_3') | ~v2_tex_2(B_92, '#skF_3') | ~v4_pre_topc(C_93, '#skF_3') | ~v4_pre_topc(B_92, '#skF_3') | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_585])).
% 3.57/1.58  tff(c_1141, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1102])).
% 3.57/1.58  tff(c_1170, plain, (v2_tex_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_1141])).
% 3.57/1.58  tff(c_1172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1170])).
% 3.57/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.58  
% 3.57/1.58  Inference rules
% 3.57/1.58  ----------------------
% 3.57/1.58  #Ref     : 0
% 3.57/1.58  #Sup     : 230
% 3.57/1.58  #Fact    : 0
% 3.57/1.58  #Define  : 0
% 3.57/1.58  #Split   : 16
% 3.57/1.58  #Chain   : 0
% 3.57/1.58  #Close   : 0
% 3.57/1.58  
% 3.57/1.58  Ordering : KBO
% 3.57/1.58  
% 3.57/1.58  Simplification rules
% 3.57/1.58  ----------------------
% 3.57/1.58  #Subsume      : 69
% 3.57/1.58  #Demod        : 817
% 3.57/1.58  #Tautology    : 88
% 3.57/1.58  #SimpNegUnit  : 6
% 3.57/1.58  #BackRed      : 1
% 3.57/1.58  
% 3.57/1.58  #Partial instantiations: 0
% 3.57/1.58  #Strategies tried      : 1
% 3.57/1.58  
% 3.57/1.58  Timing (in seconds)
% 3.57/1.58  ----------------------
% 3.57/1.59  Preprocessing        : 0.33
% 3.57/1.59  Parsing              : 0.18
% 3.57/1.59  CNF conversion       : 0.02
% 3.57/1.59  Main loop            : 0.47
% 3.57/1.59  Inferencing          : 0.16
% 3.57/1.59  Reduction            : 0.19
% 3.57/1.59  Demodulation         : 0.15
% 3.57/1.59  BG Simplification    : 0.02
% 3.57/1.59  Subsumption          : 0.08
% 3.57/1.59  Abstraction          : 0.02
% 3.57/1.59  MUC search           : 0.00
% 3.57/1.59  Cooper               : 0.00
% 3.57/1.59  Total                : 0.85
% 3.57/1.59  Index Insertion      : 0.00
% 3.57/1.59  Index Deletion       : 0.00
% 3.57/1.59  Index Matching       : 0.00
% 3.57/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
