%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:32 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 181 expanded)
%              Number of leaves         :   40 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :  141 ( 353 expanded)
%              Number of equality atoms :   31 (  69 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    ! [A_27] :
      ( v4_pre_topc(k2_struct_0(A_27),A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_46,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_22,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_86,plain,(
    ! [A_18] : m1_subset_1('#skF_5',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_22])).

tff(c_30,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_103,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_112,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_303,plain,(
    ! [A_104,B_105] :
      ( r1_tarski('#skF_3'(A_104,B_105),B_105)
      | v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_314,plain,(
    ! [B_105] :
      ( r1_tarski('#skF_3'('#skF_4',B_105),B_105)
      | v2_tex_2(B_105,'#skF_4')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_303])).

tff(c_483,plain,(
    ! [B_118] :
      ( r1_tarski('#skF_3'('#skF_4',B_118),B_118)
      | v2_tex_2(B_118,'#skF_4')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_314])).

tff(c_495,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_483])).

tff(c_504,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_495])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [A_6] :
      ( A_6 = '#skF_5'
      | ~ r1_tarski(A_6,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_10])).

tff(c_509,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_504,c_95])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_82,B_83,C_84] :
      ( k9_subset_1(A_82,B_83,C_84) = k3_xboole_0(B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_181,plain,(
    ! [A_85,B_86] : k9_subset_1(A_85,B_86,A_85) = k3_xboole_0(B_86,A_85) ),
    inference(resolution,[status(thm)],[c_57,c_167])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k9_subset_1(A_12,B_13,C_14),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_187,plain,(
    ! [B_86,A_85] :
      ( m1_subset_1(k3_xboole_0(B_86,A_85),k1_zfmisc_1(A_85))
      | ~ m1_subset_1(A_85,k1_zfmisc_1(A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_18])).

tff(c_195,plain,(
    ! [B_87,A_88] : m1_subset_1(k3_xboole_0(B_87,A_88),k1_zfmisc_1(A_88)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_187])).

tff(c_26,plain,(
    ! [C_24,B_23,A_22] :
      ( ~ v1_xboole_0(C_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_239,plain,(
    ! [A_93,A_94,B_95] :
      ( ~ v1_xboole_0(A_93)
      | ~ r2_hidden(A_94,k3_xboole_0(B_95,A_93)) ) ),
    inference(resolution,[status(thm)],[c_195,c_26])).

tff(c_267,plain,(
    ! [A_99,B_100] :
      ( ~ v1_xboole_0(A_99)
      | v1_xboole_0(k3_xboole_0(B_100,A_99)) ) ),
    inference(resolution,[status(thm)],[c_4,c_239])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_8])).

tff(c_272,plain,(
    ! [B_101,A_102] :
      ( k3_xboole_0(B_101,A_102) = '#skF_5'
      | ~ v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_267,c_78])).

tff(c_278,plain,(
    ! [B_101] : k3_xboole_0(B_101,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_272])).

tff(c_179,plain,(
    ! [A_18,B_83] : k9_subset_1(A_18,B_83,'#skF_5') = k3_xboole_0(B_83,'#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_167])).

tff(c_245,plain,(
    ! [A_96,C_97,B_98] :
      ( k9_subset_1(A_96,C_97,B_98) = k9_subset_1(A_96,B_98,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_256,plain,(
    ! [A_18,B_98] : k9_subset_1(A_18,B_98,'#skF_5') = k9_subset_1(A_18,'#skF_5',B_98) ),
    inference(resolution,[status(thm)],[c_86,c_245])).

tff(c_264,plain,(
    ! [A_18,B_98] : k9_subset_1(A_18,'#skF_5',B_98) = k3_xboole_0(B_98,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_256])).

tff(c_408,plain,(
    ! [A_18,B_98] : k9_subset_1(A_18,'#skF_5',B_98) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_264])).

tff(c_819,plain,(
    ! [A_141,B_142,D_143] :
      ( k9_subset_1(u1_struct_0(A_141),B_142,D_143) != '#skF_3'(A_141,B_142)
      | ~ v4_pre_topc(D_143,A_141)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_836,plain,(
    ! [B_142,D_143] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_142,D_143) != '#skF_3'('#skF_4',B_142)
      | ~ v4_pre_topc(D_143,'#skF_4')
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_142,'#skF_4')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_819])).

tff(c_1687,plain,(
    ! [B_189,D_190] :
      ( k9_subset_1(k2_struct_0('#skF_4'),B_189,D_190) != '#skF_3'('#skF_4',B_189)
      | ~ v4_pre_topc(D_190,'#skF_4')
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_tex_2(B_189,'#skF_4')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_112,c_112,c_836])).

tff(c_1693,plain,(
    ! [B_98] :
      ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
      | ~ v4_pre_topc(B_98,'#skF_4')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_1687])).

tff(c_1706,plain,(
    ! [B_98] :
      ( ~ v4_pre_topc(B_98,'#skF_4')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_tex_2('#skF_5','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_509,c_1693])).

tff(c_1714,plain,(
    ! [B_191] :
      ( ~ v4_pre_topc(B_191,'#skF_4')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1706])).

tff(c_1762,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_1714])).

tff(c_1765,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1762])).

tff(c_1769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.67  
% 3.57/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.67  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.57/1.67  
% 3.57/1.67  %Foreground sorts:
% 3.57/1.67  
% 3.57/1.67  
% 3.57/1.67  %Background operators:
% 3.57/1.67  
% 3.57/1.67  
% 3.57/1.67  %Foreground operators:
% 3.57/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.57/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.57/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.67  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.57/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.57/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.57/1.67  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.57/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.57/1.67  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.57/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.67  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.57/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.67  
% 3.82/1.69  tff(f_121, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.82/1.69  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.82/1.69  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.82/1.69  tff(f_48, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.82/1.69  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.82/1.69  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.82/1.69  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.82/1.69  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.82/1.69  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.82/1.69  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.82/1.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.82/1.69  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.82/1.69  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.82/1.69  tff(f_71, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.82/1.69  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.82/1.69  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.82/1.69  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.82/1.69  tff(c_32, plain, (![A_27]: (v4_pre_topc(k2_struct_0(A_27), A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.82/1.69  tff(c_14, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.82/1.69  tff(c_16, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.82/1.69  tff(c_57, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.82/1.69  tff(c_46, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.82/1.69  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.82/1.69  tff(c_68, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.82/1.69  tff(c_77, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_68])).
% 3.82/1.69  tff(c_22, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.69  tff(c_86, plain, (![A_18]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_22])).
% 3.82/1.69  tff(c_30, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.69  tff(c_103, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.82/1.69  tff(c_108, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_30, c_103])).
% 3.82/1.69  tff(c_112, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_108])).
% 3.82/1.69  tff(c_303, plain, (![A_104, B_105]: (r1_tarski('#skF_3'(A_104, B_105), B_105) | v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.82/1.69  tff(c_314, plain, (![B_105]: (r1_tarski('#skF_3'('#skF_4', B_105), B_105) | v2_tex_2(B_105, '#skF_4') | ~m1_subset_1(B_105, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_303])).
% 3.82/1.69  tff(c_483, plain, (![B_118]: (r1_tarski('#skF_3'('#skF_4', B_118), B_118) | v2_tex_2(B_118, '#skF_4') | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_314])).
% 3.82/1.69  tff(c_495, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_483])).
% 3.82/1.69  tff(c_504, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_495])).
% 3.82/1.69  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.82/1.69  tff(c_95, plain, (![A_6]: (A_6='#skF_5' | ~r1_tarski(A_6, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_10])).
% 3.82/1.69  tff(c_509, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_504, c_95])).
% 3.82/1.69  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.69  tff(c_167, plain, (![A_82, B_83, C_84]: (k9_subset_1(A_82, B_83, C_84)=k3_xboole_0(B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.82/1.69  tff(c_181, plain, (![A_85, B_86]: (k9_subset_1(A_85, B_86, A_85)=k3_xboole_0(B_86, A_85))), inference(resolution, [status(thm)], [c_57, c_167])).
% 3.82/1.69  tff(c_18, plain, (![A_12, B_13, C_14]: (m1_subset_1(k9_subset_1(A_12, B_13, C_14), k1_zfmisc_1(A_12)) | ~m1_subset_1(C_14, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.69  tff(c_187, plain, (![B_86, A_85]: (m1_subset_1(k3_xboole_0(B_86, A_85), k1_zfmisc_1(A_85)) | ~m1_subset_1(A_85, k1_zfmisc_1(A_85)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_18])).
% 3.82/1.69  tff(c_195, plain, (![B_87, A_88]: (m1_subset_1(k3_xboole_0(B_87, A_88), k1_zfmisc_1(A_88)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_187])).
% 3.82/1.69  tff(c_26, plain, (![C_24, B_23, A_22]: (~v1_xboole_0(C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(C_24)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.82/1.69  tff(c_239, plain, (![A_93, A_94, B_95]: (~v1_xboole_0(A_93) | ~r2_hidden(A_94, k3_xboole_0(B_95, A_93)))), inference(resolution, [status(thm)], [c_195, c_26])).
% 3.82/1.69  tff(c_267, plain, (![A_99, B_100]: (~v1_xboole_0(A_99) | v1_xboole_0(k3_xboole_0(B_100, A_99)))), inference(resolution, [status(thm)], [c_4, c_239])).
% 3.82/1.69  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.82/1.69  tff(c_78, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_8])).
% 3.82/1.69  tff(c_272, plain, (![B_101, A_102]: (k3_xboole_0(B_101, A_102)='#skF_5' | ~v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_267, c_78])).
% 3.82/1.69  tff(c_278, plain, (![B_101]: (k3_xboole_0(B_101, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_50, c_272])).
% 3.82/1.69  tff(c_179, plain, (![A_18, B_83]: (k9_subset_1(A_18, B_83, '#skF_5')=k3_xboole_0(B_83, '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_167])).
% 3.82/1.69  tff(c_245, plain, (![A_96, C_97, B_98]: (k9_subset_1(A_96, C_97, B_98)=k9_subset_1(A_96, B_98, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.82/1.69  tff(c_256, plain, (![A_18, B_98]: (k9_subset_1(A_18, B_98, '#skF_5')=k9_subset_1(A_18, '#skF_5', B_98))), inference(resolution, [status(thm)], [c_86, c_245])).
% 3.82/1.69  tff(c_264, plain, (![A_18, B_98]: (k9_subset_1(A_18, '#skF_5', B_98)=k3_xboole_0(B_98, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_256])).
% 3.82/1.69  tff(c_408, plain, (![A_18, B_98]: (k9_subset_1(A_18, '#skF_5', B_98)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_264])).
% 3.82/1.69  tff(c_819, plain, (![A_141, B_142, D_143]: (k9_subset_1(u1_struct_0(A_141), B_142, D_143)!='#skF_3'(A_141, B_142) | ~v4_pre_topc(D_143, A_141) | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0(A_141))) | v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.82/1.69  tff(c_836, plain, (![B_142, D_143]: (k9_subset_1(k2_struct_0('#skF_4'), B_142, D_143)!='#skF_3'('#skF_4', B_142) | ~v4_pre_topc(D_143, '#skF_4') | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_142, '#skF_4') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_819])).
% 3.82/1.69  tff(c_1687, plain, (![B_189, D_190]: (k9_subset_1(k2_struct_0('#skF_4'), B_189, D_190)!='#skF_3'('#skF_4', B_189) | ~v4_pre_topc(D_190, '#skF_4') | ~m1_subset_1(D_190, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_tex_2(B_189, '#skF_4') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_112, c_112, c_836])).
% 3.82/1.69  tff(c_1693, plain, (![B_98]: ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~v4_pre_topc(B_98, '#skF_4') | ~m1_subset_1(B_98, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_408, c_1687])).
% 3.82/1.69  tff(c_1706, plain, (![B_98]: (~v4_pre_topc(B_98, '#skF_4') | ~m1_subset_1(B_98, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_509, c_1693])).
% 3.82/1.69  tff(c_1714, plain, (![B_191]: (~v4_pre_topc(B_191, '#skF_4') | ~m1_subset_1(B_191, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_1706])).
% 3.82/1.69  tff(c_1762, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_57, c_1714])).
% 3.82/1.69  tff(c_1765, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1762])).
% 3.82/1.69  tff(c_1769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1765])).
% 3.82/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.69  
% 3.82/1.69  Inference rules
% 3.82/1.69  ----------------------
% 3.82/1.69  #Ref     : 0
% 3.82/1.69  #Sup     : 413
% 3.82/1.69  #Fact    : 0
% 3.82/1.69  #Define  : 0
% 3.82/1.69  #Split   : 2
% 3.82/1.69  #Chain   : 0
% 3.82/1.69  #Close   : 0
% 3.82/1.69  
% 3.82/1.69  Ordering : KBO
% 3.82/1.69  
% 3.82/1.69  Simplification rules
% 3.82/1.69  ----------------------
% 3.82/1.69  #Subsume      : 63
% 3.82/1.69  #Demod        : 267
% 3.82/1.69  #Tautology    : 165
% 3.82/1.69  #SimpNegUnit  : 5
% 3.82/1.69  #BackRed      : 5
% 3.82/1.69  
% 3.82/1.69  #Partial instantiations: 0
% 3.82/1.69  #Strategies tried      : 1
% 3.82/1.69  
% 3.82/1.69  Timing (in seconds)
% 3.82/1.69  ----------------------
% 3.82/1.69  Preprocessing        : 0.36
% 3.82/1.69  Parsing              : 0.18
% 3.82/1.69  CNF conversion       : 0.03
% 3.82/1.69  Main loop            : 0.51
% 3.82/1.69  Inferencing          : 0.17
% 3.82/1.69  Reduction            : 0.17
% 3.82/1.69  Demodulation         : 0.12
% 3.82/1.69  BG Simplification    : 0.03
% 3.82/1.69  Subsumption          : 0.10
% 3.82/1.69  Abstraction          : 0.03
% 3.82/1.69  MUC search           : 0.00
% 3.82/1.69  Cooper               : 0.00
% 3.82/1.69  Total                : 0.90
% 3.82/1.69  Index Insertion      : 0.00
% 3.82/1.69  Index Deletion       : 0.00
% 3.82/1.69  Index Matching       : 0.00
% 3.82/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
