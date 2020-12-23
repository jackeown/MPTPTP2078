%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:28 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 173 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 425 expanded)
%              Number of equality atoms :   19 (  55 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_54])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    ! [A_16] : m1_subset_1('#skF_6',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_252,plain,(
    ! [A_105,B_106] :
      ( r1_tarski('#skF_4'(A_105,B_106),B_106)
      | v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_269,plain,(
    ! [A_107] :
      ( r1_tarski('#skF_4'(A_107,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_60,c_252])).

tff(c_87,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [B_64,A_63] :
      ( B_64 = A_63
      | ~ r1_tarski(B_64,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_98,c_14])).

tff(c_277,plain,(
    ! [A_107] :
      ( '#skF_4'(A_107,'#skF_6') = '#skF_6'
      | ~ v1_xboole_0('#skF_6')
      | v2_tex_2('#skF_6',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_269,c_101])).

tff(c_298,plain,(
    ! [A_109] :
      ( '#skF_4'(A_109,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_277])).

tff(c_301,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_298,c_40])).

tff(c_304,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_301])).

tff(c_48,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_391,plain,(
    ! [A_116,B_117] :
      ( m1_subset_1('#skF_4'(A_116,B_117),k1_zfmisc_1(u1_struct_0(A_116)))
      | v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [B_22,A_20] :
      ( v4_pre_topc(B_22,A_20)
      | ~ v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_863,plain,(
    ! [A_170,B_171] :
      ( v4_pre_topc('#skF_4'(A_170,B_171),A_170)
      | ~ v1_xboole_0('#skF_4'(A_170,B_171))
      | ~ v2_pre_topc(A_170)
      | v2_tex_2(B_171,A_170)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_391,c_26])).

tff(c_877,plain,(
    ! [A_172] :
      ( v4_pre_topc('#skF_4'(A_172,'#skF_6'),A_172)
      | ~ v1_xboole_0('#skF_4'(A_172,'#skF_6'))
      | ~ v2_pre_topc(A_172)
      | v2_tex_2('#skF_6',A_172)
      | ~ l1_pre_topc(A_172) ) ),
    inference(resolution,[status(thm)],[c_60,c_863])).

tff(c_886,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_5')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_877])).

tff(c_888,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_44,c_304,c_886])).

tff(c_889,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_888])).

tff(c_123,plain,(
    ! [A_72,B_73,C_74] :
      ( k9_subset_1(A_72,B_73,B_73) = B_73
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [A_16,B_73] : k9_subset_1(A_16,B_73,B_73) = B_73 ),
    inference(resolution,[status(thm)],[c_60,c_123])).

tff(c_577,plain,(
    ! [A_141,B_142,D_143] :
      ( k9_subset_1(u1_struct_0(A_141),B_142,D_143) != '#skF_4'(A_141,B_142)
      | ~ v4_pre_topc(D_143,A_141)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_935,plain,(
    ! [A_182,B_183] :
      ( '#skF_4'(A_182,B_183) != B_183
      | ~ v4_pre_topc(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | v2_tex_2(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_577])).

tff(c_944,plain,(
    ! [A_182] :
      ( '#skF_4'(A_182,'#skF_6') != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_182)
      | v2_tex_2('#skF_6',A_182)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_60,c_935])).

tff(c_1023,plain,(
    ! [A_186] :
      ( '#skF_4'(A_186,'#skF_6') != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_186)
      | v2_tex_2('#skF_6',A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_944])).

tff(c_1026,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_889,c_1023])).

tff(c_1032,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_304,c_1026])).

tff(c_1034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:06:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.47  
% 3.23/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.47  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.23/1.47  
% 3.23/1.47  %Foreground sorts:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Background operators:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Foreground operators:
% 3.23/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.23/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.23/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.23/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.23/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.23/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.47  
% 3.23/1.49  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 3.23/1.49  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.23/1.49  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.23/1.49  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 3.23/1.49  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.23/1.49  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.49  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.23/1.49  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 3.23/1.49  tff(c_40, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.49  tff(c_46, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.49  tff(c_44, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.49  tff(c_54, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.23/1.49  tff(c_58, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_44, c_54])).
% 3.23/1.49  tff(c_22, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.49  tff(c_60, plain, (![A_16]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 3.23/1.49  tff(c_252, plain, (![A_105, B_106]: (r1_tarski('#skF_4'(A_105, B_106), B_106) | v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.49  tff(c_269, plain, (![A_107]: (r1_tarski('#skF_4'(A_107, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_60, c_252])).
% 3.23/1.49  tff(c_87, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.49  tff(c_98, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_87, c_2])).
% 3.23/1.49  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.49  tff(c_101, plain, (![B_64, A_63]: (B_64=A_63 | ~r1_tarski(B_64, A_63) | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_98, c_14])).
% 3.23/1.49  tff(c_277, plain, (![A_107]: ('#skF_4'(A_107, '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6') | v2_tex_2('#skF_6', A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_269, c_101])).
% 3.23/1.49  tff(c_298, plain, (![A_109]: ('#skF_4'(A_109, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_109) | ~l1_pre_topc(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_277])).
% 3.23/1.49  tff(c_301, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_298, c_40])).
% 3.23/1.49  tff(c_304, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_301])).
% 3.23/1.49  tff(c_48, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.49  tff(c_391, plain, (![A_116, B_117]: (m1_subset_1('#skF_4'(A_116, B_117), k1_zfmisc_1(u1_struct_0(A_116))) | v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.49  tff(c_26, plain, (![B_22, A_20]: (v4_pre_topc(B_22, A_20) | ~v1_xboole_0(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.49  tff(c_863, plain, (![A_170, B_171]: (v4_pre_topc('#skF_4'(A_170, B_171), A_170) | ~v1_xboole_0('#skF_4'(A_170, B_171)) | ~v2_pre_topc(A_170) | v2_tex_2(B_171, A_170) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_391, c_26])).
% 3.23/1.49  tff(c_877, plain, (![A_172]: (v4_pre_topc('#skF_4'(A_172, '#skF_6'), A_172) | ~v1_xboole_0('#skF_4'(A_172, '#skF_6')) | ~v2_pre_topc(A_172) | v2_tex_2('#skF_6', A_172) | ~l1_pre_topc(A_172))), inference(resolution, [status(thm)], [c_60, c_863])).
% 3.23/1.49  tff(c_886, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_5') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_304, c_877])).
% 3.23/1.49  tff(c_888, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_44, c_304, c_886])).
% 3.23/1.49  tff(c_889, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_888])).
% 3.23/1.49  tff(c_123, plain, (![A_72, B_73, C_74]: (k9_subset_1(A_72, B_73, B_73)=B_73 | ~m1_subset_1(C_74, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.49  tff(c_126, plain, (![A_16, B_73]: (k9_subset_1(A_16, B_73, B_73)=B_73)), inference(resolution, [status(thm)], [c_60, c_123])).
% 3.23/1.49  tff(c_577, plain, (![A_141, B_142, D_143]: (k9_subset_1(u1_struct_0(A_141), B_142, D_143)!='#skF_4'(A_141, B_142) | ~v4_pre_topc(D_143, A_141) | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0(A_141))) | v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.49  tff(c_935, plain, (![A_182, B_183]: ('#skF_4'(A_182, B_183)!=B_183 | ~v4_pre_topc(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | v2_tex_2(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(superposition, [status(thm), theory('equality')], [c_126, c_577])).
% 3.23/1.49  tff(c_944, plain, (![A_182]: ('#skF_4'(A_182, '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', A_182) | v2_tex_2('#skF_6', A_182) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_60, c_935])).
% 3.23/1.49  tff(c_1023, plain, (![A_186]: ('#skF_4'(A_186, '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', A_186) | v2_tex_2('#skF_6', A_186) | ~l1_pre_topc(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_944])).
% 3.23/1.49  tff(c_1026, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_889, c_1023])).
% 3.23/1.49  tff(c_1032, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_304, c_1026])).
% 3.23/1.49  tff(c_1034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1032])).
% 3.23/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  Inference rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Ref     : 0
% 3.23/1.49  #Sup     : 218
% 3.23/1.49  #Fact    : 2
% 3.23/1.49  #Define  : 0
% 3.23/1.49  #Split   : 1
% 3.23/1.49  #Chain   : 0
% 3.23/1.49  #Close   : 0
% 3.23/1.49  
% 3.23/1.49  Ordering : KBO
% 3.23/1.49  
% 3.23/1.49  Simplification rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Subsume      : 87
% 3.23/1.49  #Demod        : 92
% 3.23/1.49  #Tautology    : 51
% 3.23/1.49  #SimpNegUnit  : 24
% 3.23/1.49  #BackRed      : 9
% 3.23/1.49  
% 3.23/1.49  #Partial instantiations: 0
% 3.23/1.49  #Strategies tried      : 1
% 3.23/1.49  
% 3.23/1.49  Timing (in seconds)
% 3.23/1.49  ----------------------
% 3.23/1.49  Preprocessing        : 0.30
% 3.23/1.49  Parsing              : 0.16
% 3.23/1.49  CNF conversion       : 0.02
% 3.23/1.49  Main loop            : 0.42
% 3.23/1.49  Inferencing          : 0.15
% 3.23/1.49  Reduction            : 0.11
% 3.23/1.49  Demodulation         : 0.08
% 3.23/1.49  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.10
% 3.23/1.49  Abstraction          : 0.02
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.75
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
