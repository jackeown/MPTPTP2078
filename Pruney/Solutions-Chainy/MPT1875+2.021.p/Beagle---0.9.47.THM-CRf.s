%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:49 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 117 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 273 expanded)
%              Number of equality atoms :    3 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_18,plain,(
    ! [A_16] :
      ( v2_tex_2(u1_struct_0(A_16),A_16)
      | ~ v1_tdlat_3(A_16)
      | ~ m1_subset_1(u1_struct_0(A_16),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_39,plain,(
    ! [A_16] :
      ( v2_tex_2(u1_struct_0(A_16),A_16)
      | ~ v1_tdlat_3(A_16)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_18])).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_41,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_89,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_90,plain,(
    ! [A_47,C_48,B_49] :
      ( m1_subset_1(A_47,C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [A_47] :
      ( m1_subset_1(A_47,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_47,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_1'(A_31,B_32),B_32)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1('#skF_1'(A_56,B_57),B_57) ) ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_129,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_56,u1_struct_0('#skF_2')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_95,c_121])).

tff(c_142,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_61,u1_struct_0('#skF_2')),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_129])).

tff(c_150,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_22,plain,(
    ! [C_25,A_19,B_23] :
      ( v2_tex_2(C_25,A_19)
      | ~ v2_tex_2(B_23,A_19)
      | ~ r1_tarski(C_25,B_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_818,plain,(
    ! [A_172] :
      ( v2_tex_2('#skF_3',A_172)
      | ~ v2_tex_2(u1_struct_0('#skF_2'),A_172)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(resolution,[status(thm)],[c_150,c_22])).

tff(c_822,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_818])).

tff(c_825,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_822])).

tff(c_826,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_825])).

tff(c_829,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_826])).

tff(c_832,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_829])).

tff(c_834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_832])).

tff(c_837,plain,(
    ! [A_173] : ~ r2_hidden(A_173,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_846,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_837])).

tff(c_882,plain,(
    ! [C_183,A_184,B_185] :
      ( v2_tex_2(C_183,A_184)
      | ~ v2_tex_2(B_185,A_184)
      | ~ r1_tarski(C_183,B_185)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1011,plain,(
    ! [A_209,B_210] :
      ( v2_tex_2('#skF_3',A_209)
      | ~ v2_tex_2(B_210,A_209)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_846,c_882])).

tff(c_1013,plain,(
    ! [B_210] :
      ( v2_tex_2('#skF_3','#skF_2')
      | ~ v2_tex_2(B_210,'#skF_2')
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_1011])).

tff(c_1016,plain,(
    ! [B_210] :
      ( v2_tex_2('#skF_3','#skF_2')
      | ~ v2_tex_2(B_210,'#skF_2')
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1013])).

tff(c_1018,plain,(
    ! [B_211] :
      ( ~ v2_tex_2(B_211,'#skF_2')
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1016])).

tff(c_1037,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_1018])).

tff(c_1040,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_1037])).

tff(c_1043,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_1040])).

tff(c_1045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:55:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.60  
% 3.11/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.60  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.11/1.60  
% 3.11/1.60  %Foreground sorts:
% 3.11/1.60  
% 3.11/1.60  
% 3.11/1.60  %Background operators:
% 3.11/1.60  
% 3.11/1.60  
% 3.11/1.60  %Foreground operators:
% 3.11/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.60  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.11/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.11/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.11/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.60  
% 3.11/1.61  tff(f_98, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 3.11/1.61  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.11/1.61  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.11/1.61  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 3.11/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.11/1.61  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.11/1.61  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.11/1.61  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.11/1.61  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 3.11/1.61  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.11/1.61  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.11/1.61  tff(c_30, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.11/1.61  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.11/1.61  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.11/1.61  tff(c_35, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.11/1.61  tff(c_18, plain, (![A_16]: (v2_tex_2(u1_struct_0(A_16), A_16) | ~v1_tdlat_3(A_16) | ~m1_subset_1(u1_struct_0(A_16), k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.11/1.61  tff(c_39, plain, (![A_16]: (v2_tex_2(u1_struct_0(A_16), A_16) | ~v1_tdlat_3(A_16) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_18])).
% 3.11/1.61  tff(c_24, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.11/1.61  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.11/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.61  tff(c_71, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.11/1.61  tff(c_76, plain, (![A_41]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_41, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_71])).
% 3.11/1.61  tff(c_89, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_76])).
% 3.11/1.61  tff(c_90, plain, (![A_47, C_48, B_49]: (m1_subset_1(A_47, C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.61  tff(c_95, plain, (![A_47]: (m1_subset_1(A_47, u1_struct_0('#skF_2')) | ~r2_hidden(A_47, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_90])).
% 3.11/1.61  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.11/1.61  tff(c_51, plain, (![A_31, B_32]: (~r2_hidden('#skF_1'(A_31, B_32), B_32) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.61  tff(c_121, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | v1_xboole_0(B_57) | ~m1_subset_1('#skF_1'(A_56, B_57), B_57))), inference(resolution, [status(thm)], [c_12, c_51])).
% 3.11/1.61  tff(c_129, plain, (![A_56]: (r1_tarski(A_56, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_56, u1_struct_0('#skF_2')), '#skF_3'))), inference(resolution, [status(thm)], [c_95, c_121])).
% 3.11/1.61  tff(c_142, plain, (![A_61]: (r1_tarski(A_61, u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_61, u1_struct_0('#skF_2')), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_89, c_129])).
% 3.11/1.61  tff(c_150, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_142])).
% 3.11/1.61  tff(c_22, plain, (![C_25, A_19, B_23]: (v2_tex_2(C_25, A_19) | ~v2_tex_2(B_23, A_19) | ~r1_tarski(C_25, B_23) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.11/1.61  tff(c_818, plain, (![A_172]: (v2_tex_2('#skF_3', A_172) | ~v2_tex_2(u1_struct_0('#skF_2'), A_172) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_172))) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(resolution, [status(thm)], [c_150, c_22])).
% 3.11/1.61  tff(c_822, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_35, c_818])).
% 3.11/1.61  tff(c_825, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_822])).
% 3.11/1.61  tff(c_826, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_825])).
% 3.11/1.61  tff(c_829, plain, (~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_39, c_826])).
% 3.11/1.61  tff(c_832, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_829])).
% 3.11/1.61  tff(c_834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_832])).
% 3.11/1.61  tff(c_837, plain, (![A_173]: (~r2_hidden(A_173, '#skF_3'))), inference(splitRight, [status(thm)], [c_76])).
% 3.11/1.61  tff(c_846, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_837])).
% 3.11/1.61  tff(c_882, plain, (![C_183, A_184, B_185]: (v2_tex_2(C_183, A_184) | ~v2_tex_2(B_185, A_184) | ~r1_tarski(C_183, B_185) | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0(A_184))) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.11/1.61  tff(c_1011, plain, (![A_209, B_210]: (v2_tex_2('#skF_3', A_209) | ~v2_tex_2(B_210, A_209) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(resolution, [status(thm)], [c_846, c_882])).
% 3.11/1.61  tff(c_1013, plain, (![B_210]: (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(B_210, '#skF_2') | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_1011])).
% 3.11/1.61  tff(c_1016, plain, (![B_210]: (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(B_210, '#skF_2') | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1013])).
% 3.11/1.61  tff(c_1018, plain, (![B_211]: (~v2_tex_2(B_211, '#skF_2') | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_24, c_1016])).
% 3.11/1.61  tff(c_1037, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_35, c_1018])).
% 3.11/1.61  tff(c_1040, plain, (~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_39, c_1037])).
% 3.11/1.61  tff(c_1043, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_1040])).
% 3.11/1.61  tff(c_1045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1043])).
% 3.11/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.61  
% 3.11/1.61  Inference rules
% 3.11/1.61  ----------------------
% 3.11/1.61  #Ref     : 0
% 3.11/1.61  #Sup     : 223
% 3.11/1.61  #Fact    : 0
% 3.11/1.61  #Define  : 0
% 3.11/1.61  #Split   : 8
% 3.11/1.61  #Chain   : 0
% 3.11/1.61  #Close   : 0
% 3.11/1.61  
% 3.11/1.61  Ordering : KBO
% 3.11/1.61  
% 3.11/1.61  Simplification rules
% 3.11/1.61  ----------------------
% 3.11/1.61  #Subsume      : 69
% 3.11/1.61  #Demod        : 23
% 3.11/1.61  #Tautology    : 26
% 3.11/1.61  #SimpNegUnit  : 17
% 3.11/1.61  #BackRed      : 0
% 3.11/1.61  
% 3.11/1.61  #Partial instantiations: 0
% 3.11/1.61  #Strategies tried      : 1
% 3.11/1.61  
% 3.11/1.61  Timing (in seconds)
% 3.11/1.61  ----------------------
% 3.11/1.62  Preprocessing        : 0.36
% 3.11/1.62  Parsing              : 0.19
% 3.11/1.62  CNF conversion       : 0.03
% 3.11/1.62  Main loop            : 0.42
% 3.11/1.62  Inferencing          : 0.15
% 3.11/1.62  Reduction            : 0.11
% 3.11/1.62  Demodulation         : 0.07
% 3.11/1.62  BG Simplification    : 0.02
% 3.11/1.62  Subsumption          : 0.11
% 3.11/1.62  Abstraction          : 0.02
% 3.11/1.62  MUC search           : 0.00
% 3.11/1.62  Cooper               : 0.00
% 3.11/1.62  Total                : 0.81
% 3.11/1.62  Index Insertion      : 0.00
% 3.11/1.62  Index Deletion       : 0.00
% 3.11/1.62  Index Matching       : 0.00
% 3.11/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
