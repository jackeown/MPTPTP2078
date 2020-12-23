%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:58 EST 2020

% Result     : Theorem 9.46s
% Output     : CNFRefutation 9.66s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 144 expanded)
%              Number of leaves         :   39 (  66 expanded)
%              Depth                    :   21
%              Number of atoms          :  192 ( 360 expanded)
%              Number of equality atoms :   39 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k4_tarski > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_119,axiom,(
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

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_54,c_62])).

tff(c_6,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_2] : k2_xboole_0(A_2,'#skF_5') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6])).

tff(c_10,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_51,B_52] : k2_xboole_0(k1_tarski(A_51),B_52) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_105,plain,(
    ! [A_51] : k1_tarski(A_51) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_101])).

tff(c_20,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_106,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | A_15 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_20])).

tff(c_109,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(A_55,B_56)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_1'(A_15),A_15)
      | A_15 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_106,c_109])).

tff(c_48,plain,(
    ! [A_41,B_43] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_41),B_43),A_41)
      | ~ m1_subset_1(B_43,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k6_domain_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_6] : m1_subset_1('#skF_5',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_8])).

tff(c_632,plain,(
    ! [C_125,B_126,A_127] :
      ( C_125 = B_126
      | ~ r1_tarski(B_126,C_125)
      | ~ v2_tex_2(C_125,A_127)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v3_tex_2(B_126,A_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_634,plain,(
    ! [A_3,A_127] :
      ( A_3 = '#skF_5'
      | ~ v2_tex_2(A_3,A_127)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v3_tex_2('#skF_5',A_127)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_73,c_632])).

tff(c_890,plain,(
    ! [A_136,A_137] :
      ( A_136 = '#skF_5'
      | ~ v2_tex_2(A_136,A_137)
      | ~ m1_subset_1(A_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ v3_tex_2('#skF_5',A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_634])).

tff(c_8511,plain,(
    ! [A_313,B_314] :
      ( k6_domain_1(u1_struct_0(A_313),B_314) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_313),B_314),A_313)
      | ~ v3_tex_2('#skF_5',A_313)
      | ~ l1_pre_topc(A_313)
      | ~ m1_subset_1(B_314,u1_struct_0(A_313))
      | v1_xboole_0(u1_struct_0(A_313)) ) ),
    inference(resolution,[status(thm)],[c_32,c_890])).

tff(c_8952,plain,(
    ! [A_322,B_323] :
      ( k6_domain_1(u1_struct_0(A_322),B_323) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_322)
      | v1_xboole_0(u1_struct_0(A_322))
      | ~ m1_subset_1(B_323,u1_struct_0(A_322))
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322)
      | v2_struct_0(A_322) ) ),
    inference(resolution,[status(thm)],[c_48,c_8511])).

tff(c_10777,plain,(
    ! [A_353] :
      ( k6_domain_1(u1_struct_0(A_353),'#skF_1'(u1_struct_0(A_353))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_353)
      | v1_xboole_0(u1_struct_0(A_353))
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353)
      | u1_struct_0(A_353) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_113,c_8952])).

tff(c_161,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_168,plain,(
    ! [A_15] :
      ( k6_domain_1(A_15,'#skF_1'(A_15)) = k1_tarski('#skF_1'(A_15))
      | v1_xboole_0(A_15)
      | A_15 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_113,c_161])).

tff(c_10827,plain,(
    ! [A_353] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_353))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_353))
      | u1_struct_0(A_353) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_353)
      | v1_xboole_0(u1_struct_0(A_353))
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353)
      | u1_struct_0(A_353) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10777,c_168])).

tff(c_10840,plain,(
    ! [A_353] :
      ( v1_xboole_0(u1_struct_0(A_353))
      | u1_struct_0(A_353) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_353)
      | v1_xboole_0(u1_struct_0(A_353))
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353)
      | u1_struct_0(A_353) = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_10827])).

tff(c_10862,plain,(
    ! [A_356] :
      ( ~ v3_tex_2('#skF_5',A_356)
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356)
      | u1_struct_0(A_356) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_356)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10840])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_10875,plain,(
    ! [A_357] :
      ( ~ v3_tex_2('#skF_5',A_357)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357)
      | u1_struct_0(A_357) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_10862,c_72])).

tff(c_10881,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_10875])).

tff(c_10885,plain,
    ( v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_10881])).

tff(c_10886,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10885])).

tff(c_234,plain,(
    ! [A_87] :
      ( m1_subset_1('#skF_2'(A_87),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_245,plain,(
    ! [A_87] :
      ( v1_xboole_0('#skF_2'(A_87))
      | ~ v1_xboole_0(u1_struct_0(A_87))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_234,c_14])).

tff(c_10973,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10886,c_245])).

tff(c_11050,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_10973])).

tff(c_11051,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11050])).

tff(c_28,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0('#skF_2'(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_11058,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11051,c_28])).

tff(c_11064,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11058])).

tff(c_11066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.46/3.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.28  
% 9.46/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.28  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k4_tarski > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 9.46/3.28  
% 9.46/3.28  %Foreground sorts:
% 9.46/3.28  
% 9.46/3.28  
% 9.46/3.28  %Background operators:
% 9.46/3.28  
% 9.46/3.28  
% 9.46/3.28  %Foreground operators:
% 9.46/3.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.46/3.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.46/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.46/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.46/3.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.46/3.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.46/3.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.46/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.46/3.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.46/3.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.46/3.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.46/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.46/3.28  tff('#skF_5', type, '#skF_5': $i).
% 9.46/3.28  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 9.46/3.28  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.46/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.46/3.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.46/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.46/3.28  tff('#skF_4', type, '#skF_4': $i).
% 9.46/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.46/3.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.46/3.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.46/3.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.46/3.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.46/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.46/3.28  
% 9.66/3.30  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 9.66/3.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.66/3.30  tff(f_32, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.66/3.30  tff(f_37, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 9.66/3.30  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 9.66/3.30  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.66/3.30  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 9.66/3.30  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 9.66/3.30  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.66/3.30  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.66/3.30  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 9.66/3.30  tff(f_101, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.66/3.30  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 9.66/3.30  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.66/3.30  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.66/3.30  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.66/3.30  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.66/3.30  tff(c_54, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.66/3.30  tff(c_50, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.66/3.30  tff(c_62, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.66/3.30  tff(c_71, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_54, c_62])).
% 9.66/3.30  tff(c_6, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.66/3.30  tff(c_84, plain, (![A_2]: (k2_xboole_0(A_2, '#skF_5')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_6])).
% 9.66/3.30  tff(c_10, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.66/3.30  tff(c_101, plain, (![A_51, B_52]: (k2_xboole_0(k1_tarski(A_51), B_52)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_10])).
% 9.66/3.30  tff(c_105, plain, (![A_51]: (k1_tarski(A_51)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_84, c_101])).
% 9.66/3.30  tff(c_20, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.66/3.30  tff(c_106, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | A_15='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_20])).
% 9.66/3.30  tff(c_109, plain, (![A_55, B_56]: (m1_subset_1(A_55, B_56) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.66/3.30  tff(c_113, plain, (![A_15]: (m1_subset_1('#skF_1'(A_15), A_15) | A_15='#skF_5')), inference(resolution, [status(thm)], [c_106, c_109])).
% 9.66/3.30  tff(c_48, plain, (![A_41, B_43]: (v2_tex_2(k6_domain_1(u1_struct_0(A_41), B_43), A_41) | ~m1_subset_1(B_43, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.66/3.30  tff(c_32, plain, (![A_27, B_28]: (m1_subset_1(k6_domain_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.66/3.30  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.66/3.30  tff(c_81, plain, (![A_6]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_12])).
% 9.66/3.30  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.66/3.30  tff(c_73, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_8])).
% 9.66/3.30  tff(c_632, plain, (![C_125, B_126, A_127]: (C_125=B_126 | ~r1_tarski(B_126, C_125) | ~v2_tex_2(C_125, A_127) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_127))) | ~v3_tex_2(B_126, A_127) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.66/3.30  tff(c_634, plain, (![A_3, A_127]: (A_3='#skF_5' | ~v2_tex_2(A_3, A_127) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_127))) | ~v3_tex_2('#skF_5', A_127) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(resolution, [status(thm)], [c_73, c_632])).
% 9.66/3.30  tff(c_890, plain, (![A_136, A_137]: (A_136='#skF_5' | ~v2_tex_2(A_136, A_137) | ~m1_subset_1(A_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~v3_tex_2('#skF_5', A_137) | ~l1_pre_topc(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_634])).
% 9.66/3.30  tff(c_8511, plain, (![A_313, B_314]: (k6_domain_1(u1_struct_0(A_313), B_314)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_313), B_314), A_313) | ~v3_tex_2('#skF_5', A_313) | ~l1_pre_topc(A_313) | ~m1_subset_1(B_314, u1_struct_0(A_313)) | v1_xboole_0(u1_struct_0(A_313)))), inference(resolution, [status(thm)], [c_32, c_890])).
% 9.66/3.30  tff(c_8952, plain, (![A_322, B_323]: (k6_domain_1(u1_struct_0(A_322), B_323)='#skF_5' | ~v3_tex_2('#skF_5', A_322) | v1_xboole_0(u1_struct_0(A_322)) | ~m1_subset_1(B_323, u1_struct_0(A_322)) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322) | v2_struct_0(A_322))), inference(resolution, [status(thm)], [c_48, c_8511])).
% 9.66/3.30  tff(c_10777, plain, (![A_353]: (k6_domain_1(u1_struct_0(A_353), '#skF_1'(u1_struct_0(A_353)))='#skF_5' | ~v3_tex_2('#skF_5', A_353) | v1_xboole_0(u1_struct_0(A_353)) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353) | u1_struct_0(A_353)='#skF_5')), inference(resolution, [status(thm)], [c_113, c_8952])).
% 9.66/3.30  tff(c_161, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.66/3.30  tff(c_168, plain, (![A_15]: (k6_domain_1(A_15, '#skF_1'(A_15))=k1_tarski('#skF_1'(A_15)) | v1_xboole_0(A_15) | A_15='#skF_5')), inference(resolution, [status(thm)], [c_113, c_161])).
% 9.66/3.30  tff(c_10827, plain, (![A_353]: (k1_tarski('#skF_1'(u1_struct_0(A_353)))='#skF_5' | v1_xboole_0(u1_struct_0(A_353)) | u1_struct_0(A_353)='#skF_5' | ~v3_tex_2('#skF_5', A_353) | v1_xboole_0(u1_struct_0(A_353)) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353) | u1_struct_0(A_353)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10777, c_168])).
% 9.66/3.30  tff(c_10840, plain, (![A_353]: (v1_xboole_0(u1_struct_0(A_353)) | u1_struct_0(A_353)='#skF_5' | ~v3_tex_2('#skF_5', A_353) | v1_xboole_0(u1_struct_0(A_353)) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353) | u1_struct_0(A_353)='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_105, c_10827])).
% 9.66/3.30  tff(c_10862, plain, (![A_356]: (~v3_tex_2('#skF_5', A_356) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356) | v2_struct_0(A_356) | u1_struct_0(A_356)='#skF_5' | v1_xboole_0(u1_struct_0(A_356)))), inference(factorization, [status(thm), theory('equality')], [c_10840])).
% 9.66/3.30  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.66/3.30  tff(c_72, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_4])).
% 9.66/3.30  tff(c_10875, plain, (![A_357]: (~v3_tex_2('#skF_5', A_357) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357) | u1_struct_0(A_357)='#skF_5')), inference(resolution, [status(thm)], [c_10862, c_72])).
% 9.66/3.30  tff(c_10881, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_50, c_10875])).
% 9.66/3.30  tff(c_10885, plain, (v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_10881])).
% 9.66/3.30  tff(c_10886, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_60, c_10885])).
% 9.66/3.30  tff(c_234, plain, (![A_87]: (m1_subset_1('#skF_2'(A_87), k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.66/3.30  tff(c_14, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.66/3.30  tff(c_245, plain, (![A_87]: (v1_xboole_0('#skF_2'(A_87)) | ~v1_xboole_0(u1_struct_0(A_87)) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_234, c_14])).
% 9.66/3.30  tff(c_10973, plain, (v1_xboole_0('#skF_2'('#skF_4')) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10886, c_245])).
% 9.66/3.30  tff(c_11050, plain, (v1_xboole_0('#skF_2'('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_10973])).
% 9.66/3.30  tff(c_11051, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_11050])).
% 9.66/3.30  tff(c_28, plain, (![A_25]: (~v1_xboole_0('#skF_2'(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.66/3.30  tff(c_11058, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_11051, c_28])).
% 9.66/3.30  tff(c_11064, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11058])).
% 9.66/3.30  tff(c_11066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_11064])).
% 9.66/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.66/3.30  
% 9.66/3.30  Inference rules
% 9.66/3.30  ----------------------
% 9.66/3.30  #Ref     : 0
% 9.66/3.30  #Sup     : 2481
% 9.66/3.30  #Fact    : 2
% 9.66/3.30  #Define  : 0
% 9.66/3.30  #Split   : 7
% 9.66/3.30  #Chain   : 0
% 9.66/3.30  #Close   : 0
% 9.66/3.30  
% 9.66/3.30  Ordering : KBO
% 9.66/3.30  
% 9.66/3.30  Simplification rules
% 9.66/3.30  ----------------------
% 9.66/3.30  #Subsume      : 617
% 9.66/3.30  #Demod        : 2901
% 9.66/3.30  #Tautology    : 898
% 9.66/3.30  #SimpNegUnit  : 852
% 9.66/3.30  #BackRed      : 10
% 9.66/3.30  
% 9.66/3.30  #Partial instantiations: 0
% 9.66/3.30  #Strategies tried      : 1
% 9.66/3.30  
% 9.66/3.30  Timing (in seconds)
% 9.66/3.30  ----------------------
% 9.66/3.30  Preprocessing        : 0.32
% 9.66/3.30  Parsing              : 0.17
% 9.66/3.30  CNF conversion       : 0.02
% 9.66/3.30  Main loop            : 2.20
% 9.66/3.30  Inferencing          : 0.57
% 9.66/3.30  Reduction            : 0.68
% 9.66/3.30  Demodulation         : 0.45
% 9.66/3.30  BG Simplification    : 0.08
% 9.66/3.30  Subsumption          : 0.76
% 9.66/3.30  Abstraction          : 0.11
% 9.66/3.30  MUC search           : 0.00
% 9.66/3.30  Cooper               : 0.00
% 9.66/3.30  Total                : 2.56
% 9.66/3.30  Index Insertion      : 0.00
% 9.66/3.30  Index Deletion       : 0.00
% 9.66/3.30  Index Matching       : 0.00
% 9.66/3.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
