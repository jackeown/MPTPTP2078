%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:02 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 109 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 248 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_105,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(A_51,B_52)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_129,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_140,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_106,c_129])).

tff(c_327,plain,(
    ! [A_91,B_92] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_91),B_92),A_91)
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1154,plain,(
    ! [A_182] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_182))),A_182)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_182)),u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | v1_xboole_0(u1_struct_0(A_182)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_327])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_58])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_5') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),B_46) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_94,plain,(
    ! [A_45] : k1_tarski(A_45) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_90])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k1_tarski(A_11),k1_zfmisc_1(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_543,plain,(
    ! [C_119,B_120,A_121] :
      ( C_119 = B_120
      | ~ r1_tarski(B_120,C_119)
      | ~ v2_tex_2(C_119,A_121)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v3_tex_2(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_545,plain,(
    ! [A_7,A_121] :
      ( A_7 = '#skF_5'
      | ~ v2_tex_2(A_7,A_121)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v3_tex_2('#skF_5',A_121)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_64,c_543])).

tff(c_551,plain,(
    ! [A_122,A_123] :
      ( A_122 = '#skF_5'
      | ~ v2_tex_2(A_122,A_123)
      | ~ m1_subset_1(A_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v3_tex_2('#skF_5',A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_545])).

tff(c_569,plain,(
    ! [A_11,A_123] :
      ( k1_tarski(A_11) = '#skF_5'
      | ~ v2_tex_2(k1_tarski(A_11),A_123)
      | ~ v3_tex_2('#skF_5',A_123)
      | ~ l1_pre_topc(A_123)
      | ~ r2_hidden(A_11,u1_struct_0(A_123)) ) ),
    inference(resolution,[status(thm)],[c_16,c_551])).

tff(c_584,plain,(
    ! [A_11,A_123] :
      ( ~ v2_tex_2(k1_tarski(A_11),A_123)
      | ~ v3_tex_2('#skF_5',A_123)
      | ~ l1_pre_topc(A_123)
      | ~ r2_hidden(A_11,u1_struct_0(A_123)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_569])).

tff(c_1562,plain,(
    ! [A_227] :
      ( ~ v3_tex_2('#skF_5',A_227)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_227)),u1_struct_0(A_227))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_227)),u1_struct_0(A_227))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227)
      | v1_xboole_0(u1_struct_0(A_227)) ) ),
    inference(resolution,[status(thm)],[c_1154,c_584])).

tff(c_1567,plain,(
    ! [A_228] :
      ( ~ v3_tex_2('#skF_5',A_228)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_228)),u1_struct_0(A_228))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228)
      | v1_xboole_0(u1_struct_0(A_228)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1562])).

tff(c_1572,plain,(
    ! [A_229] :
      ( ~ v3_tex_2('#skF_5',A_229)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229)
      | v1_xboole_0(u1_struct_0(A_229)) ) ),
    inference(resolution,[status(thm)],[c_106,c_1567])).

tff(c_224,plain,(
    ! [A_78] :
      ( m1_subset_1('#skF_2'(A_78),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [C_20,B_19,A_18] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_299,plain,(
    ! [A_87,A_88] :
      ( ~ v1_xboole_0(u1_struct_0(A_87))
      | ~ r2_hidden(A_88,'#skF_2'(A_87))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_224,c_22])).

tff(c_304,plain,(
    ! [A_87] :
      ( ~ v1_xboole_0(u1_struct_0(A_87))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87)
      | v1_xboole_0('#skF_2'(A_87)) ) ),
    inference(resolution,[status(thm)],[c_4,c_299])).

tff(c_1585,plain,(
    ! [A_230] :
      ( v1_xboole_0('#skF_2'(A_230))
      | ~ v3_tex_2('#skF_5',A_230)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_1572,c_304])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0('#skF_2'(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1594,plain,(
    ! [A_231] :
      ( ~ v3_tex_2('#skF_5',A_231)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_1585,c_26])).

tff(c_1600,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1594])).

tff(c_1604,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1600])).

tff(c_1606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.83  
% 4.63/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.84  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 4.63/1.84  
% 4.63/1.84  %Foreground sorts:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Background operators:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Foreground operators:
% 4.63/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.63/1.84  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.63/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.63/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.63/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.63/1.84  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.63/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.84  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.63/1.84  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.63/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.63/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.63/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.84  
% 4.63/1.85  tff(f_133, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.63/1.85  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.63/1.85  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.63/1.85  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.63/1.85  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.63/1.85  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.63/1.85  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.63/1.85  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.63/1.85  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 4.63/1.85  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.63/1.85  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.63/1.85  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.63/1.85  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.63/1.85  tff(f_65, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.63/1.85  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.63/1.85  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.63/1.85  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.63/1.85  tff(c_46, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.63/1.85  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.85  tff(c_102, plain, (![A_51, B_52]: (m1_subset_1(A_51, B_52) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.85  tff(c_106, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_102])).
% 4.63/1.85  tff(c_129, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.63/1.85  tff(c_140, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_106, c_129])).
% 4.63/1.85  tff(c_327, plain, (![A_91, B_92]: (v2_tex_2(k6_domain_1(u1_struct_0(A_91), B_92), A_91) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.63/1.85  tff(c_1154, plain, (![A_182]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_182))), A_182) | ~m1_subset_1('#skF_1'(u1_struct_0(A_182)), u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | v1_xboole_0(u1_struct_0(A_182)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_327])).
% 4.63/1.85  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.63/1.85  tff(c_58, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.85  tff(c_62, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_58])).
% 4.63/1.85  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.63/1.85  tff(c_70, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8])).
% 4.63/1.85  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.63/1.85  tff(c_90, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), B_46)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12])).
% 4.63/1.85  tff(c_94, plain, (![A_45]: (k1_tarski(A_45)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_70, c_90])).
% 4.63/1.85  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k1_tarski(A_11), k1_zfmisc_1(B_12)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.85  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.85  tff(c_80, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_14])).
% 4.63/1.85  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.85  tff(c_64, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10])).
% 4.63/1.85  tff(c_543, plain, (![C_119, B_120, A_121]: (C_119=B_120 | ~r1_tarski(B_120, C_119) | ~v2_tex_2(C_119, A_121) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_121))) | ~v3_tex_2(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.85  tff(c_545, plain, (![A_7, A_121]: (A_7='#skF_5' | ~v2_tex_2(A_7, A_121) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_121))) | ~v3_tex_2('#skF_5', A_121) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_64, c_543])).
% 4.63/1.85  tff(c_551, plain, (![A_122, A_123]: (A_122='#skF_5' | ~v2_tex_2(A_122, A_123) | ~m1_subset_1(A_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~v3_tex_2('#skF_5', A_123) | ~l1_pre_topc(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_545])).
% 4.63/1.85  tff(c_569, plain, (![A_11, A_123]: (k1_tarski(A_11)='#skF_5' | ~v2_tex_2(k1_tarski(A_11), A_123) | ~v3_tex_2('#skF_5', A_123) | ~l1_pre_topc(A_123) | ~r2_hidden(A_11, u1_struct_0(A_123)))), inference(resolution, [status(thm)], [c_16, c_551])).
% 4.63/1.85  tff(c_584, plain, (![A_11, A_123]: (~v2_tex_2(k1_tarski(A_11), A_123) | ~v3_tex_2('#skF_5', A_123) | ~l1_pre_topc(A_123) | ~r2_hidden(A_11, u1_struct_0(A_123)))), inference(negUnitSimplification, [status(thm)], [c_94, c_569])).
% 4.63/1.85  tff(c_1562, plain, (![A_227]: (~v3_tex_2('#skF_5', A_227) | ~r2_hidden('#skF_1'(u1_struct_0(A_227)), u1_struct_0(A_227)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_227)), u1_struct_0(A_227)) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227) | v1_xboole_0(u1_struct_0(A_227)))), inference(resolution, [status(thm)], [c_1154, c_584])).
% 4.63/1.85  tff(c_1567, plain, (![A_228]: (~v3_tex_2('#skF_5', A_228) | ~m1_subset_1('#skF_1'(u1_struct_0(A_228)), u1_struct_0(A_228)) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228) | v1_xboole_0(u1_struct_0(A_228)))), inference(resolution, [status(thm)], [c_4, c_1562])).
% 4.63/1.85  tff(c_1572, plain, (![A_229]: (~v3_tex_2('#skF_5', A_229) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229) | v1_xboole_0(u1_struct_0(A_229)))), inference(resolution, [status(thm)], [c_106, c_1567])).
% 4.63/1.85  tff(c_224, plain, (![A_78]: (m1_subset_1('#skF_2'(A_78), k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.63/1.85  tff(c_22, plain, (![C_20, B_19, A_18]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.63/1.85  tff(c_299, plain, (![A_87, A_88]: (~v1_xboole_0(u1_struct_0(A_87)) | ~r2_hidden(A_88, '#skF_2'(A_87)) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_224, c_22])).
% 4.63/1.85  tff(c_304, plain, (![A_87]: (~v1_xboole_0(u1_struct_0(A_87)) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87) | v1_xboole_0('#skF_2'(A_87)))), inference(resolution, [status(thm)], [c_4, c_299])).
% 4.63/1.85  tff(c_1585, plain, (![A_230]: (v1_xboole_0('#skF_2'(A_230)) | ~v3_tex_2('#skF_5', A_230) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_1572, c_304])).
% 4.63/1.85  tff(c_26, plain, (![A_21]: (~v1_xboole_0('#skF_2'(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.63/1.85  tff(c_1594, plain, (![A_231]: (~v3_tex_2('#skF_5', A_231) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_1585, c_26])).
% 4.63/1.85  tff(c_1600, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1594])).
% 4.63/1.85  tff(c_1604, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1600])).
% 4.63/1.85  tff(c_1606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1604])).
% 4.63/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.85  
% 4.63/1.85  Inference rules
% 4.63/1.85  ----------------------
% 4.63/1.85  #Ref     : 0
% 4.63/1.85  #Sup     : 372
% 4.63/1.85  #Fact    : 0
% 4.63/1.85  #Define  : 0
% 4.63/1.85  #Split   : 3
% 4.63/1.85  #Chain   : 0
% 4.63/1.85  #Close   : 0
% 4.63/1.85  
% 4.63/1.85  Ordering : KBO
% 4.63/1.85  
% 4.63/1.85  Simplification rules
% 4.63/1.85  ----------------------
% 4.63/1.85  #Subsume      : 78
% 4.63/1.85  #Demod        : 56
% 4.63/1.85  #Tautology    : 86
% 4.63/1.85  #SimpNegUnit  : 23
% 4.63/1.85  #BackRed      : 3
% 4.63/1.85  
% 4.63/1.85  #Partial instantiations: 0
% 4.63/1.85  #Strategies tried      : 1
% 4.63/1.85  
% 4.63/1.85  Timing (in seconds)
% 4.63/1.85  ----------------------
% 4.63/1.85  Preprocessing        : 0.31
% 4.63/1.85  Parsing              : 0.16
% 4.63/1.85  CNF conversion       : 0.02
% 4.63/1.85  Main loop            : 0.72
% 4.63/1.85  Inferencing          : 0.26
% 4.63/1.85  Reduction            : 0.18
% 4.63/1.85  Demodulation         : 0.11
% 4.63/1.85  BG Simplification    : 0.03
% 4.63/1.85  Subsumption          : 0.20
% 4.63/1.85  Abstraction          : 0.03
% 4.63/1.86  MUC search           : 0.00
% 4.63/1.86  Cooper               : 0.00
% 4.63/1.86  Total                : 1.06
% 4.63/1.86  Index Insertion      : 0.00
% 4.63/1.86  Index Deletion       : 0.00
% 4.63/1.86  Index Matching       : 0.00
% 4.63/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
