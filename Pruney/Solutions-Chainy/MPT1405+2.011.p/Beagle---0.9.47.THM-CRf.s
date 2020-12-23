%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:31 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   58 (  92 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 165 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_62,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_66,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    ! [A_33] :
      ( l1_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_115,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_120,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_124,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_120])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_125,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_64])).

tff(c_131,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_140,plain,(
    r1_tarski('#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_125,c_131])).

tff(c_197,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_208,plain,(
    ! [A_78] : r1_tarski(A_78,A_78) ),
    inference(resolution,[status(thm)],[c_197,c_8])).

tff(c_68,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ! [A_34] :
      ( k1_tops_1(A_34,k2_struct_0(A_34)) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_682,plain,(
    ! [C_128,A_129,B_130] :
      ( m2_connsp_2(C_128,A_129,B_130)
      | ~ r1_tarski(B_130,k1_tops_1(A_129,C_128))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3215,plain,(
    ! [A_310,B_311] :
      ( m2_connsp_2(k2_struct_0(A_310),A_310,B_311)
      | ~ r1_tarski(B_311,k2_struct_0(A_310))
      | ~ m1_subset_1(k2_struct_0(A_310),k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_682])).

tff(c_8192,plain,(
    ! [A_498,B_499] :
      ( m2_connsp_2(k2_struct_0(A_498),A_498,B_499)
      | ~ r1_tarski(B_499,k2_struct_0(A_498))
      | ~ m1_subset_1(B_499,k1_zfmisc_1(u1_struct_0(A_498)))
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | ~ r1_tarski(k2_struct_0(A_498),u1_struct_0(A_498)) ) ),
    inference(resolution,[status(thm)],[c_46,c_3215])).

tff(c_8235,plain,(
    ! [B_499] :
      ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5',B_499)
      | ~ r1_tarski(B_499,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_499,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8192])).

tff(c_8862,plain,(
    ! [B_518] :
      ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5',B_518)
      | ~ r1_tarski(B_518,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_518,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_124,c_68,c_66,c_8235])).

tff(c_8928,plain,
    ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_6')
    | ~ r1_tarski('#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_125,c_8862])).

tff(c_8968,plain,(
    m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_8928])).

tff(c_8970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.83  
% 7.69/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.83  %$ m2_connsp_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 7.69/2.83  
% 7.69/2.83  %Foreground sorts:
% 7.69/2.83  
% 7.69/2.83  
% 7.69/2.83  %Background operators:
% 7.69/2.83  
% 7.69/2.83  
% 7.69/2.83  %Foreground operators:
% 7.69/2.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.69/2.83  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.69/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.69/2.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.69/2.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.69/2.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.69/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.69/2.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.69/2.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.69/2.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.69/2.83  tff('#skF_5', type, '#skF_5': $i).
% 7.69/2.83  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.69/2.83  tff('#skF_6', type, '#skF_6': $i).
% 7.69/2.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.69/2.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.69/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.69/2.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.69/2.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.69/2.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.69/2.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.69/2.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.69/2.83  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 7.69/2.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.83  
% 7.69/2.84  tff(f_150, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 7.69/2.84  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.69/2.84  tff(f_106, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.69/2.84  tff(f_102, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.69/2.84  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.69/2.84  tff(f_116, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 7.69/2.84  tff(f_130, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 7.69/2.84  tff(c_62, plain, (~m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.69/2.84  tff(c_66, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.69/2.84  tff(c_50, plain, (![A_33]: (l1_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.69/2.84  tff(c_115, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.69/2.84  tff(c_120, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_50, c_115])).
% 7.69/2.84  tff(c_124, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_120])).
% 7.69/2.84  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.69/2.84  tff(c_125, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_64])).
% 7.69/2.84  tff(c_131, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.69/2.84  tff(c_140, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_125, c_131])).
% 7.69/2.84  tff(c_197, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.69/2.84  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.69/2.84  tff(c_208, plain, (![A_78]: (r1_tarski(A_78, A_78))), inference(resolution, [status(thm)], [c_197, c_8])).
% 7.69/2.84  tff(c_68, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.69/2.84  tff(c_46, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.69/2.84  tff(c_52, plain, (![A_34]: (k1_tops_1(A_34, k2_struct_0(A_34))=k2_struct_0(A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.69/2.84  tff(c_682, plain, (![C_128, A_129, B_130]: (m2_connsp_2(C_128, A_129, B_130) | ~r1_tarski(B_130, k1_tops_1(A_129, C_128)) | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.69/2.84  tff(c_3215, plain, (![A_310, B_311]: (m2_connsp_2(k2_struct_0(A_310), A_310, B_311) | ~r1_tarski(B_311, k2_struct_0(A_310)) | ~m1_subset_1(k2_struct_0(A_310), k1_zfmisc_1(u1_struct_0(A_310))) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310))), inference(superposition, [status(thm), theory('equality')], [c_52, c_682])).
% 7.69/2.84  tff(c_8192, plain, (![A_498, B_499]: (m2_connsp_2(k2_struct_0(A_498), A_498, B_499) | ~r1_tarski(B_499, k2_struct_0(A_498)) | ~m1_subset_1(B_499, k1_zfmisc_1(u1_struct_0(A_498))) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | ~r1_tarski(k2_struct_0(A_498), u1_struct_0(A_498)))), inference(resolution, [status(thm)], [c_46, c_3215])).
% 7.69/2.84  tff(c_8235, plain, (![B_499]: (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', B_499) | ~r1_tarski(B_499, k2_struct_0('#skF_5')) | ~m1_subset_1(B_499, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_124, c_8192])).
% 7.69/2.84  tff(c_8862, plain, (![B_518]: (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', B_518) | ~r1_tarski(B_518, k2_struct_0('#skF_5')) | ~m1_subset_1(B_518, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_124, c_68, c_66, c_8235])).
% 7.69/2.84  tff(c_8928, plain, (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', '#skF_6') | ~r1_tarski('#skF_6', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_125, c_8862])).
% 7.69/2.84  tff(c_8968, plain, (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_8928])).
% 7.69/2.84  tff(c_8970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_8968])).
% 7.69/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.84  
% 7.69/2.84  Inference rules
% 7.69/2.84  ----------------------
% 7.69/2.84  #Ref     : 15
% 7.69/2.84  #Sup     : 2073
% 7.69/2.84  #Fact    : 0
% 7.69/2.84  #Define  : 0
% 7.69/2.84  #Split   : 21
% 7.69/2.84  #Chain   : 0
% 7.69/2.84  #Close   : 0
% 7.69/2.84  
% 7.69/2.84  Ordering : KBO
% 7.69/2.84  
% 7.69/2.84  Simplification rules
% 7.69/2.84  ----------------------
% 7.69/2.84  #Subsume      : 683
% 7.69/2.84  #Demod        : 599
% 7.69/2.84  #Tautology    : 453
% 7.69/2.84  #SimpNegUnit  : 301
% 7.69/2.84  #BackRed      : 44
% 7.69/2.84  
% 7.69/2.84  #Partial instantiations: 0
% 7.69/2.84  #Strategies tried      : 1
% 7.69/2.84  
% 7.69/2.84  Timing (in seconds)
% 7.69/2.84  ----------------------
% 7.69/2.85  Preprocessing        : 0.35
% 7.69/2.85  Parsing              : 0.19
% 7.69/2.85  CNF conversion       : 0.02
% 7.69/2.85  Main loop            : 1.72
% 7.69/2.85  Inferencing          : 0.51
% 7.69/2.85  Reduction            : 0.55
% 7.69/2.85  Demodulation         : 0.35
% 7.69/2.85  BG Simplification    : 0.05
% 7.69/2.85  Subsumption          : 0.46
% 7.69/2.85  Abstraction          : 0.07
% 7.69/2.85  MUC search           : 0.00
% 7.69/2.85  Cooper               : 0.00
% 7.69/2.85  Total                : 2.09
% 7.69/2.85  Index Insertion      : 0.00
% 7.69/2.85  Index Deletion       : 0.00
% 7.69/2.85  Index Matching       : 0.00
% 7.69/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
