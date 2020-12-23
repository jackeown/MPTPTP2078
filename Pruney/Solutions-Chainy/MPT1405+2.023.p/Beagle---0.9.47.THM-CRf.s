%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:33 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 174 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  128 ( 370 expanded)
%              Number of equality atoms :    8 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_28,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_37,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_49,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_55,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_59,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_30])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ r2_hidden(A_41,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_78])).

tff(c_95,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_103,plain,(
    ! [A_49,C_50,B_51] :
      ( m1_subset_1(A_49,C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,(
    ! [A_49] :
      ( m1_subset_1(A_49,k2_struct_0('#skF_2'))
      | ~ r2_hidden(A_49,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_72,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1('#skF_1'(A_58,B_59),B_59) ) ),
    inference(resolution,[status(thm)],[c_72,c_4])).

tff(c_146,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_58,k2_struct_0('#skF_2')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_108,c_138])).

tff(c_152,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,k2_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_60,k2_struct_0('#skF_2')),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_146])).

tff(c_161,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_22,plain,(
    ! [A_18] :
      ( k1_tops_1(A_18,k2_struct_0(A_18)) = k2_struct_0(A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_306,plain,(
    ! [C_87,A_88,B_89] :
      ( m2_connsp_2(C_87,A_88,B_89)
      | ~ r1_tarski(B_89,k1_tops_1(A_88,C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_493,plain,(
    ! [A_116,B_117] :
      ( m2_connsp_2(k2_struct_0(A_116),A_116,B_117)
      | ~ r1_tarski(B_117,k2_struct_0(A_116))
      | ~ m1_subset_1(k2_struct_0(A_116),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_306])).

tff(c_495,plain,(
    ! [B_117] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_117)
      | ~ r1_tarski(B_117,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_493])).

tff(c_498,plain,(
    ! [B_118] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_118)
      | ~ r1_tarski(B_118,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_34,c_32,c_59,c_37,c_495])).

tff(c_509,plain,
    ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_498])).

tff(c_518,plain,(
    m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_509])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_518])).

tff(c_523,plain,(
    ! [A_119] : ~ r2_hidden(A_119,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_533,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_523])).

tff(c_695,plain,(
    ! [C_155,A_156,B_157] :
      ( m2_connsp_2(C_155,A_156,B_157)
      | ~ r1_tarski(B_157,k1_tops_1(A_156,C_155))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_756,plain,(
    ! [C_169,A_170] :
      ( m2_connsp_2(C_169,A_170,'#skF_3')
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_533,c_695])).

tff(c_764,plain,(
    ! [C_169] :
      ( m2_connsp_2(C_169,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_756])).

tff(c_773,plain,(
    ! [C_171] :
      ( m2_connsp_2(C_171,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_60,c_59,c_764])).

tff(c_788,plain,(
    m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_773])).

tff(c_795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.48  
% 3.35/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.48  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.35/1.48  
% 3.35/1.48  %Foreground sorts:
% 3.35/1.48  
% 3.35/1.48  
% 3.35/1.48  %Background operators:
% 3.35/1.48  
% 3.35/1.48  
% 3.35/1.48  %Foreground operators:
% 3.35/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.35/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.35/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.35/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.35/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.35/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.35/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.35/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.35/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.48  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.35/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.48  
% 3.35/1.50  tff(f_96, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.35/1.50  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.35/1.50  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.35/1.50  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.35/1.50  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.35/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.35/1.50  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.35/1.50  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.35/1.50  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.35/1.50  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.35/1.50  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.35/1.50  tff(c_28, plain, (~m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.50  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.35/1.50  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.35/1.50  tff(c_37, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.35/1.50  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.50  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.50  tff(c_20, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.35/1.50  tff(c_49, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.35/1.50  tff(c_55, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_20, c_49])).
% 3.35/1.50  tff(c_59, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_55])).
% 3.35/1.50  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.50  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_30])).
% 3.35/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.50  tff(c_78, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.35/1.50  tff(c_83, plain, (![A_41]: (~v1_xboole_0(k2_struct_0('#skF_2')) | ~r2_hidden(A_41, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_78])).
% 3.35/1.50  tff(c_95, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_83])).
% 3.35/1.50  tff(c_103, plain, (![A_49, C_50, B_51]: (m1_subset_1(A_49, C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.35/1.50  tff(c_108, plain, (![A_49]: (m1_subset_1(A_49, k2_struct_0('#skF_2')) | ~r2_hidden(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_103])).
% 3.35/1.50  tff(c_72, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.35/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.50  tff(c_138, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | v1_xboole_0(B_59) | ~m1_subset_1('#skF_1'(A_58, B_59), B_59))), inference(resolution, [status(thm)], [c_72, c_4])).
% 3.35/1.50  tff(c_146, plain, (![A_58]: (r1_tarski(A_58, k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_58, k2_struct_0('#skF_2')), '#skF_3'))), inference(resolution, [status(thm)], [c_108, c_138])).
% 3.35/1.50  tff(c_152, plain, (![A_60]: (r1_tarski(A_60, k2_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_60, k2_struct_0('#skF_2')), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_95, c_146])).
% 3.35/1.50  tff(c_161, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_152])).
% 3.35/1.50  tff(c_22, plain, (![A_18]: (k1_tops_1(A_18, k2_struct_0(A_18))=k2_struct_0(A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.35/1.50  tff(c_306, plain, (![C_87, A_88, B_89]: (m2_connsp_2(C_87, A_88, B_89) | ~r1_tarski(B_89, k1_tops_1(A_88, C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.50  tff(c_493, plain, (![A_116, B_117]: (m2_connsp_2(k2_struct_0(A_116), A_116, B_117) | ~r1_tarski(B_117, k2_struct_0(A_116)) | ~m1_subset_1(k2_struct_0(A_116), k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_22, c_306])).
% 3.35/1.50  tff(c_495, plain, (![B_117]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_117) | ~r1_tarski(B_117, k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_493])).
% 3.35/1.50  tff(c_498, plain, (![B_118]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_118) | ~r1_tarski(B_118, k2_struct_0('#skF_2')) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_34, c_32, c_59, c_37, c_495])).
% 3.35/1.50  tff(c_509, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_498])).
% 3.35/1.50  tff(c_518, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_509])).
% 3.35/1.50  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_518])).
% 3.35/1.50  tff(c_523, plain, (![A_119]: (~r2_hidden(A_119, '#skF_3'))), inference(splitRight, [status(thm)], [c_83])).
% 3.35/1.50  tff(c_533, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_523])).
% 3.35/1.50  tff(c_695, plain, (![C_155, A_156, B_157]: (m2_connsp_2(C_155, A_156, B_157) | ~r1_tarski(B_157, k1_tops_1(A_156, C_155)) | ~m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.50  tff(c_756, plain, (![C_169, A_170]: (m2_connsp_2(C_169, A_170, '#skF_3') | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170))), inference(resolution, [status(thm)], [c_533, c_695])).
% 3.35/1.50  tff(c_764, plain, (![C_169]: (m2_connsp_2(C_169, '#skF_2', '#skF_3') | ~m1_subset_1(C_169, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_756])).
% 3.35/1.50  tff(c_773, plain, (![C_171]: (m2_connsp_2(C_171, '#skF_2', '#skF_3') | ~m1_subset_1(C_171, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_60, c_59, c_764])).
% 3.35/1.50  tff(c_788, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_37, c_773])).
% 3.35/1.50  tff(c_795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_788])).
% 3.35/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.50  
% 3.35/1.50  Inference rules
% 3.35/1.50  ----------------------
% 3.35/1.50  #Ref     : 0
% 3.35/1.50  #Sup     : 170
% 3.35/1.50  #Fact    : 0
% 3.35/1.50  #Define  : 0
% 3.35/1.50  #Split   : 7
% 3.35/1.50  #Chain   : 0
% 3.35/1.50  #Close   : 0
% 3.35/1.50  
% 3.35/1.50  Ordering : KBO
% 3.35/1.50  
% 3.35/1.50  Simplification rules
% 3.35/1.50  ----------------------
% 3.35/1.50  #Subsume      : 33
% 3.35/1.50  #Demod        : 28
% 3.35/1.50  #Tautology    : 26
% 3.35/1.50  #SimpNegUnit  : 6
% 3.35/1.50  #BackRed      : 1
% 3.35/1.50  
% 3.35/1.50  #Partial instantiations: 0
% 3.35/1.50  #Strategies tried      : 1
% 3.35/1.50  
% 3.35/1.50  Timing (in seconds)
% 3.35/1.50  ----------------------
% 3.35/1.50  Preprocessing        : 0.32
% 3.35/1.50  Parsing              : 0.17
% 3.35/1.50  CNF conversion       : 0.02
% 3.35/1.50  Main loop            : 0.40
% 3.35/1.50  Inferencing          : 0.15
% 3.35/1.50  Reduction            : 0.11
% 3.35/1.50  Demodulation         : 0.07
% 3.35/1.50  BG Simplification    : 0.02
% 3.35/1.50  Subsumption          : 0.09
% 3.35/1.50  Abstraction          : 0.02
% 3.35/1.50  MUC search           : 0.00
% 3.35/1.50  Cooper               : 0.00
% 3.35/1.50  Total                : 0.76
% 3.35/1.50  Index Insertion      : 0.00
% 3.35/1.50  Index Deletion       : 0.00
% 3.35/1.50  Index Matching       : 0.00
% 3.35/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
