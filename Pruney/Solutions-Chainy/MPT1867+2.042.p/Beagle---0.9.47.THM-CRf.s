%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:27 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 121 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 256 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_95,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_52,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_65,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_26,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    ! [A_17] : m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_26])).

tff(c_295,plain,(
    ! [A_111,B_112] :
      ( r1_tarski('#skF_4'(A_111,B_112),B_112)
      | v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_312,plain,(
    ! [A_113] :
      ( r1_tarski('#skF_4'(A_113,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_77,c_295])).

tff(c_113,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_66,B_67] :
      ( ~ v1_xboole_0(A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [B_67,A_66] :
      ( B_67 = A_66
      | ~ r1_tarski(B_67,A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_124,c_16])).

tff(c_322,plain,(
    ! [A_113] :
      ( '#skF_4'(A_113,'#skF_6') = '#skF_6'
      | ~ v1_xboole_0('#skF_6')
      | v2_tex_2('#skF_6',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_312,c_127])).

tff(c_344,plain,(
    ! [A_115] :
      ( '#skF_4'(A_115,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_322])).

tff(c_44,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_347,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_344,c_44])).

tff(c_350,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_347])).

tff(c_247,plain,(
    ! [B_102,A_103] :
      ( v4_pre_topc(B_102,A_103)
      | ~ v1_xboole_0(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_263,plain,(
    ! [A_103] :
      ( v4_pre_topc('#skF_6',A_103)
      | ~ v1_xboole_0('#skF_6')
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_77,c_247])).

tff(c_269,plain,(
    ! [A_103] :
      ( v4_pre_topc('#skF_6',A_103)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_263])).

tff(c_22,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_22])).

tff(c_189,plain,(
    ! [A_86,B_87,C_88] :
      ( k9_subset_1(A_86,B_87,C_88) = k3_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,(
    ! [A_17,B_87] : k9_subset_1(A_17,B_87,'#skF_6') = k3_xboole_0(B_87,'#skF_6') ),
    inference(resolution,[status(thm)],[c_77,c_189])).

tff(c_197,plain,(
    ! [A_17,B_87] : k9_subset_1(A_17,B_87,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_194])).

tff(c_622,plain,(
    ! [A_144,B_145,D_146] :
      ( k9_subset_1(u1_struct_0(A_144),B_145,D_146) != '#skF_4'(A_144,B_145)
      | ~ v4_pre_topc(D_146,A_144)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | v2_tex_2(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_625,plain,(
    ! [A_144,B_87] :
      ( '#skF_4'(A_144,B_87) != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_144)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_144)))
      | v2_tex_2(B_87,A_144)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_622])).

tff(c_791,plain,(
    ! [A_160,B_161] :
      ( '#skF_4'(A_160,B_161) != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_160)
      | v2_tex_2(B_161,A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_625])).

tff(c_805,plain,(
    ! [A_162] :
      ( '#skF_4'(A_162,'#skF_6') != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_162)
      | v2_tex_2('#skF_6',A_162)
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_77,c_791])).

tff(c_810,plain,(
    ! [A_163] :
      ( '#skF_4'(A_163,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_163)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_269,c_805])).

tff(c_813,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_810,c_44])).

tff(c_817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_350,c_813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.52  
% 3.01/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.52  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.01/1.52  
% 3.01/1.52  %Foreground sorts:
% 3.01/1.52  
% 3.01/1.52  
% 3.01/1.52  %Background operators:
% 3.01/1.52  
% 3.01/1.52  
% 3.01/1.52  %Foreground operators:
% 3.01/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.01/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.01/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.52  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.01/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.01/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.52  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.01/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.01/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.01/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.01/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.01/1.52  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.01/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.52  
% 3.01/1.54  tff(f_110, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.01/1.54  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.01/1.54  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.01/1.54  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.01/1.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.01/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.01/1.54  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.01/1.54  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.01/1.54  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.01/1.54  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.01/1.54  tff(c_52, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.01/1.54  tff(c_50, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.01/1.54  tff(c_48, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.01/1.54  tff(c_65, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.01/1.54  tff(c_74, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_48, c_65])).
% 3.01/1.54  tff(c_26, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.54  tff(c_77, plain, (![A_17]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_26])).
% 3.01/1.54  tff(c_295, plain, (![A_111, B_112]: (r1_tarski('#skF_4'(A_111, B_112), B_112) | v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.01/1.54  tff(c_312, plain, (![A_113]: (r1_tarski('#skF_4'(A_113, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_77, c_295])).
% 3.01/1.54  tff(c_113, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.01/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.54  tff(c_124, plain, (![A_66, B_67]: (~v1_xboole_0(A_66) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.01/1.54  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.54  tff(c_127, plain, (![B_67, A_66]: (B_67=A_66 | ~r1_tarski(B_67, A_66) | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_124, c_16])).
% 3.01/1.54  tff(c_322, plain, (![A_113]: ('#skF_4'(A_113, '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6') | v2_tex_2('#skF_6', A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_312, c_127])).
% 3.01/1.54  tff(c_344, plain, (![A_115]: ('#skF_4'(A_115, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_115) | ~l1_pre_topc(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_322])).
% 3.01/1.54  tff(c_44, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.01/1.54  tff(c_347, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_344, c_44])).
% 3.01/1.54  tff(c_350, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_347])).
% 3.01/1.54  tff(c_247, plain, (![B_102, A_103]: (v4_pre_topc(B_102, A_103) | ~v1_xboole_0(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.54  tff(c_263, plain, (![A_103]: (v4_pre_topc('#skF_6', A_103) | ~v1_xboole_0('#skF_6') | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(resolution, [status(thm)], [c_77, c_247])).
% 3.01/1.54  tff(c_269, plain, (![A_103]: (v4_pre_topc('#skF_6', A_103) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_263])).
% 3.01/1.54  tff(c_22, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.01/1.54  tff(c_76, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_22])).
% 3.01/1.54  tff(c_189, plain, (![A_86, B_87, C_88]: (k9_subset_1(A_86, B_87, C_88)=k3_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.01/1.54  tff(c_194, plain, (![A_17, B_87]: (k9_subset_1(A_17, B_87, '#skF_6')=k3_xboole_0(B_87, '#skF_6'))), inference(resolution, [status(thm)], [c_77, c_189])).
% 3.01/1.54  tff(c_197, plain, (![A_17, B_87]: (k9_subset_1(A_17, B_87, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_194])).
% 3.01/1.54  tff(c_622, plain, (![A_144, B_145, D_146]: (k9_subset_1(u1_struct_0(A_144), B_145, D_146)!='#skF_4'(A_144, B_145) | ~v4_pre_topc(D_146, A_144) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_144))) | v2_tex_2(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.01/1.54  tff(c_625, plain, (![A_144, B_87]: ('#skF_4'(A_144, B_87)!='#skF_6' | ~v4_pre_topc('#skF_6', A_144) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_144))) | v2_tex_2(B_87, A_144) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(superposition, [status(thm), theory('equality')], [c_197, c_622])).
% 3.01/1.54  tff(c_791, plain, (![A_160, B_161]: ('#skF_4'(A_160, B_161)!='#skF_6' | ~v4_pre_topc('#skF_6', A_160) | v2_tex_2(B_161, A_160) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_625])).
% 3.01/1.54  tff(c_805, plain, (![A_162]: ('#skF_4'(A_162, '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', A_162) | v2_tex_2('#skF_6', A_162) | ~l1_pre_topc(A_162))), inference(resolution, [status(thm)], [c_77, c_791])).
% 3.01/1.54  tff(c_810, plain, (![A_163]: ('#skF_4'(A_163, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_163) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(resolution, [status(thm)], [c_269, c_805])).
% 3.01/1.54  tff(c_813, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_810, c_44])).
% 3.01/1.54  tff(c_817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_350, c_813])).
% 3.01/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.54  
% 3.01/1.54  Inference rules
% 3.01/1.54  ----------------------
% 3.01/1.54  #Ref     : 0
% 3.01/1.54  #Sup     : 164
% 3.01/1.54  #Fact    : 2
% 3.01/1.54  #Define  : 0
% 3.01/1.54  #Split   : 1
% 3.01/1.54  #Chain   : 0
% 3.01/1.54  #Close   : 0
% 3.01/1.54  
% 3.01/1.54  Ordering : KBO
% 3.01/1.54  
% 3.01/1.54  Simplification rules
% 3.01/1.54  ----------------------
% 3.01/1.54  #Subsume      : 70
% 3.01/1.54  #Demod        : 58
% 3.01/1.54  #Tautology    : 50
% 3.01/1.54  #SimpNegUnit  : 15
% 3.01/1.54  #BackRed      : 11
% 3.01/1.54  
% 3.01/1.54  #Partial instantiations: 0
% 3.01/1.54  #Strategies tried      : 1
% 3.01/1.54  
% 3.01/1.54  Timing (in seconds)
% 3.01/1.54  ----------------------
% 3.01/1.54  Preprocessing        : 0.33
% 3.01/1.54  Parsing              : 0.16
% 3.01/1.54  CNF conversion       : 0.03
% 3.01/1.54  Main loop            : 0.38
% 3.01/1.54  Inferencing          : 0.14
% 3.01/1.54  Reduction            : 0.11
% 3.01/1.54  Demodulation         : 0.07
% 3.01/1.54  BG Simplification    : 0.02
% 3.01/1.54  Subsumption          : 0.09
% 3.01/1.54  Abstraction          : 0.02
% 3.01/1.54  MUC search           : 0.00
% 3.01/1.54  Cooper               : 0.00
% 3.01/1.54  Total                : 0.74
% 3.01/1.54  Index Insertion      : 0.00
% 3.01/1.54  Index Deletion       : 0.00
% 3.01/1.54  Index Matching       : 0.00
% 3.01/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
