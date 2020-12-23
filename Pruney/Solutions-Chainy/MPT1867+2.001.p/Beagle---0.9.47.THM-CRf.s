%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:22 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 172 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  125 ( 350 expanded)
%              Number of equality atoms :   23 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_93,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_61,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_52])).

tff(c_18,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_18])).

tff(c_206,plain,(
    ! [A_79,B_80] :
      ( r1_tarski('#skF_2'(A_79,B_80),B_80)
      | v2_tex_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_217,plain,(
    ! [A_82] :
      ( r1_tarski('#skF_2'(A_82,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_71,c_206])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_86,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_63,c_86])).

tff(c_227,plain,(
    ! [A_83] :
      ( '#skF_2'(A_83,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_217,c_91])).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_230,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_227,c_38])).

tff(c_233,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_230])).

tff(c_159,plain,(
    ! [B_73,A_74] :
      ( v3_pre_topc(B_73,A_74)
      | ~ v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_171,plain,(
    ! [A_74] :
      ( v3_pre_topc('#skF_4',A_74)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_71,c_159])).

tff(c_176,plain,(
    ! [A_74] :
      ( v3_pre_topc('#skF_4',A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_171])).

tff(c_114,plain,(
    ! [A_63,B_64,C_65] :
      ( k9_subset_1(A_63,B_64,C_65) = k3_xboole_0(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_117,plain,(
    ! [A_11,B_64] : k9_subset_1(A_11,B_64,'#skF_4') = k3_xboole_0(B_64,'#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_114])).

tff(c_127,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k9_subset_1(A_68,B_69,C_70),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,(
    ! [B_64,A_11] :
      ( m1_subset_1(k3_xboole_0(B_64,'#skF_4'),k1_zfmisc_1(A_11))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_127])).

tff(c_143,plain,(
    ! [B_71,A_72] : m1_subset_1(k3_xboole_0(B_71,'#skF_4'),k1_zfmisc_1(A_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_137])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    ! [B_71,A_72] :
      ( v1_xboole_0(k3_xboole_0(B_71,'#skF_4'))
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_143,c_20])).

tff(c_154,plain,(
    ! [A_72] : ~ v1_xboole_0(A_72) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_42])).

tff(c_177,plain,(
    ! [B_75] : v1_xboole_0(k3_xboole_0(B_75,'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_62,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_181,plain,(
    ! [B_75] : k3_xboole_0(B_75,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_177,c_62])).

tff(c_184,plain,(
    ! [A_11,B_64] : k9_subset_1(A_11,B_64,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_117])).

tff(c_335,plain,(
    ! [A_106,B_107,D_108] :
      ( k9_subset_1(u1_struct_0(A_106),B_107,D_108) != '#skF_2'(A_106,B_107)
      | ~ v3_pre_topc(D_108,A_106)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_338,plain,(
    ! [A_106,B_64] :
      ( '#skF_2'(A_106,B_64) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_106)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_106)))
      | v2_tex_2(B_64,A_106)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_335])).

tff(c_454,plain,(
    ! [A_125,B_126] :
      ( '#skF_2'(A_125,B_126) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_125)
      | v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_338])).

tff(c_473,plain,(
    ! [A_127] :
      ( '#skF_2'(A_127,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_127)
      | v2_tex_2('#skF_4',A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_71,c_454])).

tff(c_478,plain,(
    ! [A_128] :
      ( '#skF_2'(A_128,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_128)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_176,c_473])).

tff(c_481,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_478,c_38])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_233,c_481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.36  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.61/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.61/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.36  
% 2.61/1.37  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.61/1.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.61/1.37  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.61/1.37  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.61/1.37  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.61/1.37  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.37  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.61/1.37  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.61/1.37  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.61/1.37  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.61/1.37  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.37  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.37  tff(c_42, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.37  tff(c_52, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.61/1.37  tff(c_61, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_52])).
% 2.61/1.37  tff(c_18, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.61/1.37  tff(c_71, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_18])).
% 2.61/1.37  tff(c_206, plain, (![A_79, B_80]: (r1_tarski('#skF_2'(A_79, B_80), B_80) | v2_tex_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.61/1.37  tff(c_217, plain, (![A_82]: (r1_tarski('#skF_2'(A_82, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_71, c_206])).
% 2.61/1.37  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.37  tff(c_63, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_12])).
% 2.61/1.37  tff(c_86, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.37  tff(c_91, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(resolution, [status(thm)], [c_63, c_86])).
% 2.61/1.37  tff(c_227, plain, (![A_83]: ('#skF_2'(A_83, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_217, c_91])).
% 2.61/1.37  tff(c_38, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.37  tff(c_230, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_227, c_38])).
% 2.61/1.37  tff(c_233, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_230])).
% 2.61/1.37  tff(c_159, plain, (![B_73, A_74]: (v3_pre_topc(B_73, A_74) | ~v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.37  tff(c_171, plain, (![A_74]: (v3_pre_topc('#skF_4', A_74) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(resolution, [status(thm)], [c_71, c_159])).
% 2.61/1.37  tff(c_176, plain, (![A_74]: (v3_pre_topc('#skF_4', A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_171])).
% 2.61/1.37  tff(c_114, plain, (![A_63, B_64, C_65]: (k9_subset_1(A_63, B_64, C_65)=k3_xboole_0(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.61/1.37  tff(c_117, plain, (![A_11, B_64]: (k9_subset_1(A_11, B_64, '#skF_4')=k3_xboole_0(B_64, '#skF_4'))), inference(resolution, [status(thm)], [c_71, c_114])).
% 2.61/1.37  tff(c_127, plain, (![A_68, B_69, C_70]: (m1_subset_1(k9_subset_1(A_68, B_69, C_70), k1_zfmisc_1(A_68)) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.37  tff(c_137, plain, (![B_64, A_11]: (m1_subset_1(k3_xboole_0(B_64, '#skF_4'), k1_zfmisc_1(A_11)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_127])).
% 2.61/1.37  tff(c_143, plain, (![B_71, A_72]: (m1_subset_1(k3_xboole_0(B_71, '#skF_4'), k1_zfmisc_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_137])).
% 2.61/1.37  tff(c_20, plain, (![B_14, A_12]: (v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.37  tff(c_153, plain, (![B_71, A_72]: (v1_xboole_0(k3_xboole_0(B_71, '#skF_4')) | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_143, c_20])).
% 2.61/1.37  tff(c_154, plain, (![A_72]: (~v1_xboole_0(A_72))), inference(splitLeft, [status(thm)], [c_153])).
% 2.61/1.37  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_42])).
% 2.61/1.37  tff(c_177, plain, (![B_75]: (v1_xboole_0(k3_xboole_0(B_75, '#skF_4')))), inference(splitRight, [status(thm)], [c_153])).
% 2.61/1.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.61/1.37  tff(c_62, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_4])).
% 2.61/1.37  tff(c_181, plain, (![B_75]: (k3_xboole_0(B_75, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_177, c_62])).
% 2.61/1.37  tff(c_184, plain, (![A_11, B_64]: (k9_subset_1(A_11, B_64, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_117])).
% 2.61/1.37  tff(c_335, plain, (![A_106, B_107, D_108]: (k9_subset_1(u1_struct_0(A_106), B_107, D_108)!='#skF_2'(A_106, B_107) | ~v3_pre_topc(D_108, A_106) | ~m1_subset_1(D_108, k1_zfmisc_1(u1_struct_0(A_106))) | v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.61/1.37  tff(c_338, plain, (![A_106, B_64]: ('#skF_2'(A_106, B_64)!='#skF_4' | ~v3_pre_topc('#skF_4', A_106) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_106))) | v2_tex_2(B_64, A_106) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(superposition, [status(thm), theory('equality')], [c_184, c_335])).
% 2.61/1.37  tff(c_454, plain, (![A_125, B_126]: ('#skF_2'(A_125, B_126)!='#skF_4' | ~v3_pre_topc('#skF_4', A_125) | v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_338])).
% 2.61/1.37  tff(c_473, plain, (![A_127]: ('#skF_2'(A_127, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_127) | v2_tex_2('#skF_4', A_127) | ~l1_pre_topc(A_127))), inference(resolution, [status(thm)], [c_71, c_454])).
% 2.61/1.37  tff(c_478, plain, (![A_128]: ('#skF_2'(A_128, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_128) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(resolution, [status(thm)], [c_176, c_473])).
% 2.61/1.37  tff(c_481, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_478, c_38])).
% 2.61/1.37  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_233, c_481])).
% 2.61/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.37  
% 2.61/1.37  Inference rules
% 2.61/1.37  ----------------------
% 2.61/1.37  #Ref     : 0
% 2.61/1.37  #Sup     : 95
% 2.61/1.37  #Fact    : 0
% 2.61/1.37  #Define  : 0
% 2.61/1.37  #Split   : 1
% 2.61/1.37  #Chain   : 0
% 2.61/1.37  #Close   : 0
% 2.61/1.37  
% 2.61/1.37  Ordering : KBO
% 2.61/1.37  
% 2.61/1.37  Simplification rules
% 2.61/1.37  ----------------------
% 2.61/1.37  #Subsume      : 8
% 2.61/1.37  #Demod        : 63
% 2.61/1.37  #Tautology    : 39
% 2.61/1.37  #SimpNegUnit  : 4
% 2.61/1.37  #BackRed      : 7
% 2.61/1.37  
% 2.61/1.37  #Partial instantiations: 0
% 2.61/1.37  #Strategies tried      : 1
% 2.61/1.37  
% 2.61/1.37  Timing (in seconds)
% 2.61/1.37  ----------------------
% 2.61/1.38  Preprocessing        : 0.32
% 2.61/1.38  Parsing              : 0.17
% 2.61/1.38  CNF conversion       : 0.02
% 2.61/1.38  Main loop            : 0.28
% 2.61/1.38  Inferencing          : 0.10
% 2.61/1.38  Reduction            : 0.08
% 2.61/1.38  Demodulation         : 0.06
% 2.61/1.38  BG Simplification    : 0.02
% 2.61/1.38  Subsumption          : 0.06
% 2.61/1.38  Abstraction          : 0.02
% 2.61/1.38  MUC search           : 0.00
% 2.61/1.38  Cooper               : 0.00
% 2.61/1.38  Total                : 0.64
% 2.61/1.38  Index Insertion      : 0.00
% 2.61/1.38  Index Deletion       : 0.00
% 2.61/1.38  Index Matching       : 0.00
% 2.61/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
