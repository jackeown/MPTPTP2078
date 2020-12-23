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
% DateTime   : Thu Dec  3 10:29:33 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 272 expanded)
%              Number of equality atoms :   34 (  67 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc6_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_52])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_5') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    ! [A_16] : m1_subset_1('#skF_5',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_691,plain,(
    ! [A_104,B_105] :
      ( r1_tarski('#skF_3'(A_104,B_105),B_105)
      | v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_699,plain,(
    ! [A_106] :
      ( r1_tarski('#skF_3'(A_106,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_58,c_691])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k1_xboole_0
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = '#skF_5'
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_702,plain,(
    ! [A_106] :
      ( k4_xboole_0('#skF_3'(A_106,'#skF_5'),'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_699,c_128])).

tff(c_709,plain,(
    ! [A_107] :
      ( '#skF_3'(A_107,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_702])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_712,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_709,c_40])).

tff(c_715,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_712])).

tff(c_24,plain,(
    ! [A_20] :
      ( v4_pre_topc('#skF_1'(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_1'(A_20),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_83,plain,(
    ! [A_54,B_55] : r1_tarski(k4_xboole_0(A_54,B_55),A_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_83])).

tff(c_129,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = '#skF_5'
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_140,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_90,c_129])).

tff(c_170,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_170])).

tff(c_207,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_202])).

tff(c_553,plain,(
    ! [A_88,B_89,C_90] :
      ( k9_subset_1(A_88,B_89,C_90) = k3_xboole_0(B_89,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_557,plain,(
    ! [A_16,B_89] : k9_subset_1(A_16,B_89,'#skF_5') = k3_xboole_0(B_89,'#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_553])).

tff(c_560,plain,(
    ! [A_16,B_89] : k9_subset_1(A_16,B_89,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_557])).

tff(c_561,plain,(
    ! [A_91,C_92,B_93] :
      ( k9_subset_1(A_91,C_92,B_93) = k9_subset_1(A_91,B_93,C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_567,plain,(
    ! [A_16,B_93] : k9_subset_1(A_16,B_93,'#skF_5') = k9_subset_1(A_16,'#skF_5',B_93) ),
    inference(resolution,[status(thm)],[c_58,c_561])).

tff(c_575,plain,(
    ! [A_16,B_93] : k9_subset_1(A_16,'#skF_5',B_93) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_567])).

tff(c_1015,plain,(
    ! [A_123,B_124,D_125] :
      ( k9_subset_1(u1_struct_0(A_123),B_124,D_125) != '#skF_3'(A_123,B_124)
      | ~ v4_pre_topc(D_125,A_123)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1024,plain,(
    ! [A_123,B_93] :
      ( '#skF_3'(A_123,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc(B_93,A_123)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2('#skF_5',A_123)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_1015])).

tff(c_1035,plain,(
    ! [A_128,B_129] :
      ( '#skF_3'(A_128,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | v2_tex_2('#skF_5',A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1024])).

tff(c_1073,plain,(
    ! [A_134] :
      ( '#skF_3'(A_134,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_1'(A_134),A_134)
      | v2_tex_2('#skF_5',A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_26,c_1035])).

tff(c_1078,plain,(
    ! [A_135] :
      ( '#skF_3'(A_135,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_24,c_1073])).

tff(c_1081,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1078,c_40])).

tff(c_1085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_715,c_1081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:19:00 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.38  
% 2.93/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.38  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.93/1.38  
% 2.93/1.38  %Foreground sorts:
% 2.93/1.38  
% 2.93/1.38  
% 2.93/1.38  %Background operators:
% 2.93/1.38  
% 2.93/1.38  
% 2.93/1.38  %Foreground operators:
% 2.93/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.93/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.93/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.93/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.93/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.93/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.93/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.93/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.93/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.38  
% 2.93/1.40  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.93/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.93/1.40  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.93/1.40  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.93/1.40  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.93/1.40  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.93/1.40  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc6_pre_topc)).
% 2.93/1.40  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.93/1.40  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.93/1.40  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.93/1.40  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.93/1.40  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.93/1.40  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.93/1.40  tff(c_44, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.93/1.40  tff(c_52, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.93/1.40  tff(c_56, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_52])).
% 2.93/1.40  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.40  tff(c_63, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10])).
% 2.93/1.40  tff(c_20, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.93/1.40  tff(c_58, plain, (![A_16]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 2.93/1.40  tff(c_691, plain, (![A_104, B_105]: (r1_tarski('#skF_3'(A_104, B_105), B_105) | v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.40  tff(c_699, plain, (![A_106]: (r1_tarski('#skF_3'(A_106, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_106) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_58, c_691])).
% 2.93/1.40  tff(c_6, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k1_xboole_0 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.40  tff(c_128, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)='#skF_5' | ~r1_tarski(A_2, B_3))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6])).
% 2.93/1.40  tff(c_702, plain, (![A_106]: (k4_xboole_0('#skF_3'(A_106, '#skF_5'), '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_106) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_699, c_128])).
% 2.93/1.40  tff(c_709, plain, (![A_107]: ('#skF_3'(A_107, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_107) | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_702])).
% 2.93/1.40  tff(c_40, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.93/1.40  tff(c_712, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_709, c_40])).
% 2.93/1.40  tff(c_715, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_712])).
% 2.93/1.40  tff(c_24, plain, (![A_20]: (v4_pre_topc('#skF_1'(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.93/1.40  tff(c_26, plain, (![A_20]: (m1_subset_1('#skF_1'(A_20), k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.93/1.40  tff(c_83, plain, (![A_54, B_55]: (r1_tarski(k4_xboole_0(A_54, B_55), A_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.40  tff(c_90, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_63, c_83])).
% 2.93/1.40  tff(c_129, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)='#skF_5' | ~r1_tarski(A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6])).
% 2.93/1.40  tff(c_140, plain, (![A_6]: (k4_xboole_0(A_6, A_6)='#skF_5')), inference(resolution, [status(thm)], [c_90, c_129])).
% 2.93/1.40  tff(c_170, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.40  tff(c_202, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_170])).
% 2.93/1.40  tff(c_207, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_202])).
% 2.93/1.40  tff(c_553, plain, (![A_88, B_89, C_90]: (k9_subset_1(A_88, B_89, C_90)=k3_xboole_0(B_89, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.40  tff(c_557, plain, (![A_16, B_89]: (k9_subset_1(A_16, B_89, '#skF_5')=k3_xboole_0(B_89, '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_553])).
% 2.93/1.40  tff(c_560, plain, (![A_16, B_89]: (k9_subset_1(A_16, B_89, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_557])).
% 2.93/1.40  tff(c_561, plain, (![A_91, C_92, B_93]: (k9_subset_1(A_91, C_92, B_93)=k9_subset_1(A_91, B_93, C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.93/1.40  tff(c_567, plain, (![A_16, B_93]: (k9_subset_1(A_16, B_93, '#skF_5')=k9_subset_1(A_16, '#skF_5', B_93))), inference(resolution, [status(thm)], [c_58, c_561])).
% 2.93/1.40  tff(c_575, plain, (![A_16, B_93]: (k9_subset_1(A_16, '#skF_5', B_93)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_567])).
% 2.93/1.40  tff(c_1015, plain, (![A_123, B_124, D_125]: (k9_subset_1(u1_struct_0(A_123), B_124, D_125)!='#skF_3'(A_123, B_124) | ~v4_pre_topc(D_125, A_123) | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.40  tff(c_1024, plain, (![A_123, B_93]: ('#skF_3'(A_123, '#skF_5')!='#skF_5' | ~v4_pre_topc(B_93, A_123) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2('#skF_5', A_123) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(superposition, [status(thm), theory('equality')], [c_575, c_1015])).
% 2.93/1.40  tff(c_1035, plain, (![A_128, B_129]: ('#skF_3'(A_128, '#skF_5')!='#skF_5' | ~v4_pre_topc(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | v2_tex_2('#skF_5', A_128) | ~l1_pre_topc(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1024])).
% 2.93/1.40  tff(c_1073, plain, (![A_134]: ('#skF_3'(A_134, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_1'(A_134), A_134) | v2_tex_2('#skF_5', A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(resolution, [status(thm)], [c_26, c_1035])).
% 2.93/1.40  tff(c_1078, plain, (![A_135]: ('#skF_3'(A_135, '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', A_135) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(resolution, [status(thm)], [c_24, c_1073])).
% 2.93/1.40  tff(c_1081, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1078, c_40])).
% 2.93/1.40  tff(c_1085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_715, c_1081])).
% 2.93/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.40  
% 2.93/1.40  Inference rules
% 2.93/1.40  ----------------------
% 2.93/1.40  #Ref     : 0
% 2.93/1.40  #Sup     : 245
% 2.93/1.40  #Fact    : 0
% 2.93/1.40  #Define  : 0
% 2.93/1.40  #Split   : 0
% 2.93/1.40  #Chain   : 0
% 2.93/1.40  #Close   : 0
% 2.93/1.40  
% 2.93/1.40  Ordering : KBO
% 2.93/1.40  
% 2.93/1.40  Simplification rules
% 2.93/1.40  ----------------------
% 2.93/1.40  #Subsume      : 3
% 2.93/1.40  #Demod        : 252
% 2.93/1.40  #Tautology    : 173
% 2.93/1.40  #SimpNegUnit  : 2
% 2.93/1.40  #BackRed      : 2
% 2.93/1.40  
% 2.93/1.40  #Partial instantiations: 0
% 2.93/1.40  #Strategies tried      : 1
% 2.93/1.40  
% 2.93/1.40  Timing (in seconds)
% 2.93/1.40  ----------------------
% 2.93/1.40  Preprocessing        : 0.30
% 2.93/1.40  Parsing              : 0.16
% 2.93/1.40  CNF conversion       : 0.02
% 2.93/1.40  Main loop            : 0.36
% 2.93/1.40  Inferencing          : 0.14
% 2.93/1.40  Reduction            : 0.12
% 2.93/1.40  Demodulation         : 0.09
% 2.93/1.40  BG Simplification    : 0.02
% 2.93/1.40  Subsumption          : 0.05
% 2.93/1.40  Abstraction          : 0.02
% 2.93/1.40  MUC search           : 0.00
% 2.93/1.40  Cooper               : 0.00
% 2.93/1.40  Total                : 0.69
% 2.93/1.40  Index Insertion      : 0.00
% 2.93/1.40  Index Deletion       : 0.00
% 2.93/1.40  Index Matching       : 0.00
% 2.93/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
