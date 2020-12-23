%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:06 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   46 (  56 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 128 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( m1_connsp_2(B,A,C)
                 => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_762,plain,(
    ! [B_91,A_92,C_93] :
      ( r2_hidden(B_91,k1_tops_1(A_92,C_93))
      | ~ m1_connsp_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_91,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_764,plain,(
    ! [B_91] :
      ( r2_hidden(B_91,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_762])).

tff(c_767,plain,(
    ! [B_91] :
      ( r2_hidden(B_91,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_764])).

tff(c_769,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_767])).

tff(c_55,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tops_1(A_38,B_39),B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_60,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_57])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    k2_xboole_0(k1_tops_1('#skF_3','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_20])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,k1_tops_1('#skF_3','#skF_4'))
      | r2_hidden(D_6,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_6])).

tff(c_787,plain,(
    ! [B_95] :
      ( r2_hidden(B_95,'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_3',B_95)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_769,c_74])).

tff(c_790,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_787])).

tff(c_793,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_790])).

tff(c_795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.51  
% 2.94/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.52  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.94/1.52  
% 2.94/1.52  %Foreground sorts:
% 2.94/1.52  
% 2.94/1.52  
% 2.94/1.52  %Background operators:
% 2.94/1.52  
% 2.94/1.52  
% 2.94/1.52  %Foreground operators:
% 2.94/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.52  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.94/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.94/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.94/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.94/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.94/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.52  
% 2.94/1.53  tff(f_94, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 2.94/1.53  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.94/1.53  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.94/1.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.94/1.53  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.94/1.53  tff(c_30, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.94/1.53  tff(c_32, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.94/1.53  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.94/1.53  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.94/1.53  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.94/1.53  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.94/1.53  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.94/1.53  tff(c_762, plain, (![B_91, A_92, C_93]: (r2_hidden(B_91, k1_tops_1(A_92, C_93)) | ~m1_connsp_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_91, u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.53  tff(c_764, plain, (![B_91]: (r2_hidden(B_91, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_762])).
% 2.94/1.53  tff(c_767, plain, (![B_91]: (r2_hidden(B_91, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_764])).
% 2.94/1.53  tff(c_769, plain, (![B_94]: (r2_hidden(B_94, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_767])).
% 2.94/1.53  tff(c_55, plain, (![A_38, B_39]: (r1_tarski(k1_tops_1(A_38, B_39), B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.53  tff(c_57, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.94/1.53  tff(c_60, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_57])).
% 2.94/1.53  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.53  tff(c_64, plain, (k2_xboole_0(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_20])).
% 2.94/1.53  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.94/1.53  tff(c_74, plain, (![D_6]: (~r2_hidden(D_6, k1_tops_1('#skF_3', '#skF_4')) | r2_hidden(D_6, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_6])).
% 2.94/1.53  tff(c_787, plain, (![B_95]: (r2_hidden(B_95, '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_3', B_95) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_769, c_74])).
% 2.94/1.53  tff(c_790, plain, (r2_hidden('#skF_5', '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_787])).
% 2.94/1.53  tff(c_793, plain, (r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_790])).
% 2.94/1.53  tff(c_795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_793])).
% 2.94/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.53  
% 2.94/1.53  Inference rules
% 2.94/1.53  ----------------------
% 2.94/1.53  #Ref     : 0
% 2.94/1.53  #Sup     : 140
% 2.94/1.53  #Fact    : 6
% 2.94/1.53  #Define  : 0
% 2.94/1.53  #Split   : 0
% 2.94/1.53  #Chain   : 0
% 2.94/1.53  #Close   : 0
% 2.94/1.53  
% 2.94/1.53  Ordering : KBO
% 2.94/1.53  
% 2.94/1.53  Simplification rules
% 2.94/1.53  ----------------------
% 2.94/1.53  #Subsume      : 25
% 2.94/1.53  #Demod        : 41
% 2.94/1.53  #Tautology    : 42
% 2.94/1.53  #SimpNegUnit  : 3
% 2.94/1.53  #BackRed      : 3
% 2.94/1.53  
% 2.94/1.53  #Partial instantiations: 0
% 2.94/1.53  #Strategies tried      : 1
% 2.94/1.53  
% 2.94/1.53  Timing (in seconds)
% 2.94/1.53  ----------------------
% 2.94/1.53  Preprocessing        : 0.36
% 2.94/1.53  Parsing              : 0.18
% 2.94/1.53  CNF conversion       : 0.03
% 2.94/1.53  Main loop            : 0.37
% 2.94/1.53  Inferencing          : 0.14
% 2.94/1.53  Reduction            : 0.09
% 2.94/1.53  Demodulation         : 0.07
% 2.94/1.53  BG Simplification    : 0.02
% 2.94/1.53  Subsumption          : 0.09
% 2.94/1.53  Abstraction          : 0.02
% 2.94/1.53  MUC search           : 0.00
% 2.94/1.53  Cooper               : 0.00
% 2.94/1.53  Total                : 0.76
% 2.94/1.53  Index Insertion      : 0.00
% 2.94/1.53  Index Deletion       : 0.00
% 2.94/1.53  Index Matching       : 0.00
% 2.94/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
