%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 110 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  152 ( 239 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_107,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_26,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_104,plain,(
    ! [A_64] :
      ( v1_xboole_0(A_64)
      | r2_hidden('#skF_1'(A_64),A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,(
    ! [A_64] :
      ( m1_subset_1('#skF_1'(A_64),A_64)
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [A_81,B_82] :
      ( k6_domain_1(A_81,B_82) = k1_tarski(B_82)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_189,plain,(
    ! [A_64] :
      ( k6_domain_1(A_64,'#skF_1'(A_64)) = k1_tarski('#skF_1'(A_64))
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_111,c_175])).

tff(c_322,plain,(
    ! [A_119,B_120] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_119),B_120),A_119)
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_960,plain,(
    ! [A_200] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_200))),A_200)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_200)),u1_struct_0(A_200))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200)
      | v1_xboole_0(u1_struct_0(A_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_322])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_76,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_2'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_55,B_56] : k2_xboole_0(k1_tarski(A_55),B_56) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_55] : k1_tarski(A_55) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_93,plain,(
    ! [A_55] : k1_tarski(A_55) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_74])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [A_9] : m1_subset_1('#skF_5',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_12])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_8])).

tff(c_756,plain,(
    ! [C_166,B_167,A_168] :
      ( C_166 = B_167
      | ~ r1_tarski(B_167,C_166)
      | ~ v2_tex_2(C_166,A_168)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ v3_tex_2(B_167,A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_758,plain,(
    ! [A_6,A_168] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_168)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ v3_tex_2('#skF_5',A_168)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_97,c_756])).

tff(c_762,plain,(
    ! [A_169,A_170] :
      ( A_169 = '#skF_5'
      | ~ v2_tex_2(A_169,A_170)
      | ~ m1_subset_1(A_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ v3_tex_2('#skF_5',A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_758])).

tff(c_809,plain,(
    ! [A_10,A_170] :
      ( k1_tarski(A_10) = '#skF_5'
      | ~ v2_tex_2(k1_tarski(A_10),A_170)
      | ~ v3_tex_2('#skF_5',A_170)
      | ~ l1_pre_topc(A_170)
      | ~ r2_hidden(A_10,u1_struct_0(A_170)) ) ),
    inference(resolution,[status(thm)],[c_14,c_762])).

tff(c_835,plain,(
    ! [A_10,A_170] :
      ( ~ v2_tex_2(k1_tarski(A_10),A_170)
      | ~ v3_tex_2('#skF_5',A_170)
      | ~ l1_pre_topc(A_170)
      | ~ r2_hidden(A_10,u1_struct_0(A_170)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_809])).

tff(c_1495,plain,(
    ! [A_247] :
      ( ~ v3_tex_2('#skF_5',A_247)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_247)),u1_struct_0(A_247))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_247)),u1_struct_0(A_247))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247)
      | v1_xboole_0(u1_struct_0(A_247)) ) ),
    inference(resolution,[status(thm)],[c_960,c_835])).

tff(c_1500,plain,(
    ! [A_248] :
      ( ~ v3_tex_2('#skF_5',A_248)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_248)),u1_struct_0(A_248))
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248)
      | v1_xboole_0(u1_struct_0(A_248)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1495])).

tff(c_1505,plain,(
    ! [A_249] :
      ( ~ v3_tex_2('#skF_5',A_249)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249)
      | v1_xboole_0(u1_struct_0(A_249)) ) ),
    inference(resolution,[status(thm)],[c_111,c_1500])).

tff(c_28,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1514,plain,(
    ! [A_250] :
      ( ~ l1_struct_0(A_250)
      | ~ v3_tex_2('#skF_5',A_250)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(resolution,[status(thm)],[c_1505,c_28])).

tff(c_1520,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1514])).

tff(c_1524,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1520])).

tff(c_1525,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1524])).

tff(c_1636,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1525])).

tff(c_1640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.73  
% 4.42/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.74  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 4.42/1.74  
% 4.42/1.74  %Foreground sorts:
% 4.42/1.74  
% 4.42/1.74  
% 4.42/1.74  %Background operators:
% 4.42/1.74  
% 4.42/1.74  
% 4.42/1.74  %Foreground operators:
% 4.42/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.42/1.74  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.42/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/1.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.42/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.74  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.42/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.42/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.42/1.74  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.42/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.42/1.74  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.42/1.74  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.42/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.42/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.42/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.42/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.42/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.42/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.42/1.74  
% 4.50/1.75  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.50/1.75  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.50/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.50/1.75  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.50/1.75  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.50/1.75  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.50/1.75  tff(f_70, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.50/1.75  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.50/1.75  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.50/1.75  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 4.50/1.75  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.50/1.75  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.50/1.75  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.50/1.75  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.50/1.75  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.50/1.75  tff(c_26, plain, (![A_31]: (l1_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.50/1.75  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.50/1.75  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.50/1.75  tff(c_46, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.50/1.75  tff(c_104, plain, (![A_64]: (v1_xboole_0(A_64) | r2_hidden('#skF_1'(A_64), A_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.75  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.50/1.75  tff(c_111, plain, (![A_64]: (m1_subset_1('#skF_1'(A_64), A_64) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_104, c_16])).
% 4.50/1.75  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.75  tff(c_175, plain, (![A_81, B_82]: (k6_domain_1(A_81, B_82)=k1_tarski(B_82) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.50/1.75  tff(c_189, plain, (![A_64]: (k6_domain_1(A_64, '#skF_1'(A_64))=k1_tarski('#skF_1'(A_64)) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_111, c_175])).
% 4.50/1.75  tff(c_322, plain, (![A_119, B_120]: (v2_tex_2(k6_domain_1(u1_struct_0(A_119), B_120), A_119) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.50/1.75  tff(c_960, plain, (![A_200]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_200))), A_200) | ~m1_subset_1('#skF_1'(u1_struct_0(A_200)), u1_struct_0(A_200)) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200) | v1_xboole_0(u1_struct_0(A_200)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_322])).
% 4.50/1.75  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.50/1.75  tff(c_76, plain, (![A_58]: (r2_hidden('#skF_2'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.50/1.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.75  tff(c_81, plain, (![A_59]: (~v1_xboole_0(A_59) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_76, c_2])).
% 4.50/1.75  tff(c_85, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_81])).
% 4.50/1.75  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.75  tff(c_70, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.50/1.75  tff(c_74, plain, (![A_55]: (k1_tarski(A_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 4.50/1.75  tff(c_93, plain, (![A_55]: (k1_tarski(A_55)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_74])).
% 4.50/1.75  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.50/1.75  tff(c_12, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.50/1.75  tff(c_95, plain, (![A_9]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_12])).
% 4.50/1.75  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.75  tff(c_97, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_8])).
% 4.50/1.75  tff(c_756, plain, (![C_166, B_167, A_168]: (C_166=B_167 | ~r1_tarski(B_167, C_166) | ~v2_tex_2(C_166, A_168) | ~m1_subset_1(C_166, k1_zfmisc_1(u1_struct_0(A_168))) | ~v3_tex_2(B_167, A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.50/1.75  tff(c_758, plain, (![A_6, A_168]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_168) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_168))) | ~v3_tex_2('#skF_5', A_168) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_97, c_756])).
% 4.50/1.75  tff(c_762, plain, (![A_169, A_170]: (A_169='#skF_5' | ~v2_tex_2(A_169, A_170) | ~m1_subset_1(A_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~v3_tex_2('#skF_5', A_170) | ~l1_pre_topc(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_758])).
% 4.50/1.75  tff(c_809, plain, (![A_10, A_170]: (k1_tarski(A_10)='#skF_5' | ~v2_tex_2(k1_tarski(A_10), A_170) | ~v3_tex_2('#skF_5', A_170) | ~l1_pre_topc(A_170) | ~r2_hidden(A_10, u1_struct_0(A_170)))), inference(resolution, [status(thm)], [c_14, c_762])).
% 4.50/1.75  tff(c_835, plain, (![A_10, A_170]: (~v2_tex_2(k1_tarski(A_10), A_170) | ~v3_tex_2('#skF_5', A_170) | ~l1_pre_topc(A_170) | ~r2_hidden(A_10, u1_struct_0(A_170)))), inference(negUnitSimplification, [status(thm)], [c_93, c_809])).
% 4.50/1.75  tff(c_1495, plain, (![A_247]: (~v3_tex_2('#skF_5', A_247) | ~r2_hidden('#skF_1'(u1_struct_0(A_247)), u1_struct_0(A_247)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_247)), u1_struct_0(A_247)) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247) | v1_xboole_0(u1_struct_0(A_247)))), inference(resolution, [status(thm)], [c_960, c_835])).
% 4.50/1.75  tff(c_1500, plain, (![A_248]: (~v3_tex_2('#skF_5', A_248) | ~m1_subset_1('#skF_1'(u1_struct_0(A_248)), u1_struct_0(A_248)) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248) | v1_xboole_0(u1_struct_0(A_248)))), inference(resolution, [status(thm)], [c_4, c_1495])).
% 4.50/1.75  tff(c_1505, plain, (![A_249]: (~v3_tex_2('#skF_5', A_249) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249) | v1_xboole_0(u1_struct_0(A_249)))), inference(resolution, [status(thm)], [c_111, c_1500])).
% 4.50/1.75  tff(c_28, plain, (![A_32]: (~v1_xboole_0(u1_struct_0(A_32)) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.50/1.75  tff(c_1514, plain, (![A_250]: (~l1_struct_0(A_250) | ~v3_tex_2('#skF_5', A_250) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(resolution, [status(thm)], [c_1505, c_28])).
% 4.50/1.75  tff(c_1520, plain, (~l1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1514])).
% 4.50/1.75  tff(c_1524, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1520])).
% 4.50/1.75  tff(c_1525, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_1524])).
% 4.50/1.75  tff(c_1636, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1525])).
% 4.50/1.75  tff(c_1640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1636])).
% 4.50/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.75  
% 4.50/1.75  Inference rules
% 4.50/1.75  ----------------------
% 4.50/1.75  #Ref     : 0
% 4.50/1.75  #Sup     : 337
% 4.50/1.75  #Fact    : 0
% 4.50/1.75  #Define  : 0
% 4.50/1.75  #Split   : 0
% 4.50/1.75  #Chain   : 0
% 4.50/1.75  #Close   : 0
% 4.50/1.75  
% 4.50/1.75  Ordering : KBO
% 4.50/1.75  
% 4.50/1.75  Simplification rules
% 4.50/1.75  ----------------------
% 4.50/1.75  #Subsume      : 6
% 4.50/1.75  #Demod        : 18
% 4.50/1.75  #Tautology    : 57
% 4.50/1.75  #SimpNegUnit  : 5
% 4.50/1.75  #BackRed      : 7
% 4.50/1.75  
% 4.50/1.75  #Partial instantiations: 0
% 4.50/1.75  #Strategies tried      : 1
% 4.50/1.75  
% 4.50/1.75  Timing (in seconds)
% 4.50/1.75  ----------------------
% 4.50/1.76  Preprocessing        : 0.33
% 4.50/1.76  Parsing              : 0.18
% 4.50/1.76  CNF conversion       : 0.02
% 4.50/1.76  Main loop            : 0.66
% 4.50/1.76  Inferencing          : 0.24
% 4.50/1.76  Reduction            : 0.17
% 4.50/1.76  Demodulation         : 0.11
% 4.50/1.76  BG Simplification    : 0.03
% 4.50/1.76  Subsumption          : 0.15
% 4.50/1.76  Abstraction          : 0.04
% 4.50/1.76  MUC search           : 0.00
% 4.50/1.76  Cooper               : 0.00
% 4.50/1.76  Total                : 1.02
% 4.50/1.76  Index Insertion      : 0.00
% 4.50/1.76  Index Deletion       : 0.00
% 4.50/1.76  Index Matching       : 0.00
% 4.50/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
