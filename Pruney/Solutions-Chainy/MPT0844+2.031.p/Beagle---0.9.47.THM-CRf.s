%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:44 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 110 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_58,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,B_40)
      | ~ r2_hidden(C_41,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [C_45] :
      ( ~ r2_hidden(C_45,'#skF_4')
      | ~ r2_hidden(C_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_58])).

tff(c_94,plain,(
    ! [A_47] :
      ( ~ r2_hidden('#skF_1'(A_47,'#skF_3'),'#skF_4')
      | r1_xboole_0(A_47,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_99,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_38,plain,(
    ! [C_33,A_34,B_35] :
      ( v4_relat_1(C_33,A_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_14])).

tff(c_48,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_45])).

tff(c_62,plain,(
    ! [C_42,A_43,B_44] :
      ( k7_relat_1(k7_relat_1(C_42,A_43),B_44) = k1_xboole_0
      | ~ r1_xboole_0(A_43,B_44)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    ! [B_44] :
      ( k7_relat_1('#skF_5',B_44) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_44)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_81,plain,(
    ! [B_44] :
      ( k7_relat_1('#skF_5',B_44) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_77])).

tff(c_112,plain,(
    k7_relat_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_81])).

tff(c_136,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k5_relset_1(A_50,B_51,C_52,D_53) = k7_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_139,plain,(
    ! [D_53] : k5_relset_1('#skF_4','#skF_2','#skF_5',D_53) = k7_relat_1('#skF_5',D_53) ),
    inference(resolution,[status(thm)],[c_26,c_136])).

tff(c_22,plain,(
    k5_relset_1('#skF_4','#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_140,plain,(
    k7_relat_1('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_22])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:20:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.86/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.86/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.17  
% 1.96/1.19  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.96/1.19  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 1.96/1.19  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.96/1.19  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.96/1.19  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.96/1.19  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.96/1.19  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.96/1.19  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.96/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.19  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.19  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.96/1.19  tff(c_58, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, B_40) | ~r2_hidden(C_41, A_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.19  tff(c_82, plain, (![C_45]: (~r2_hidden(C_45, '#skF_4') | ~r2_hidden(C_45, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_58])).
% 1.96/1.19  tff(c_94, plain, (![A_47]: (~r2_hidden('#skF_1'(A_47, '#skF_3'), '#skF_4') | r1_xboole_0(A_47, '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_82])).
% 1.96/1.19  tff(c_99, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_94])).
% 1.96/1.19  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.19  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.96/1.19  tff(c_28, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.96/1.19  tff(c_31, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 1.96/1.19  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 1.96/1.19  tff(c_38, plain, (![C_33, A_34, B_35]: (v4_relat_1(C_33, A_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.19  tff(c_42, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_38])).
% 1.96/1.19  tff(c_14, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.19  tff(c_45, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_14])).
% 1.96/1.19  tff(c_48, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_45])).
% 1.96/1.19  tff(c_62, plain, (![C_42, A_43, B_44]: (k7_relat_1(k7_relat_1(C_42, A_43), B_44)=k1_xboole_0 | ~r1_xboole_0(A_43, B_44) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.19  tff(c_77, plain, (![B_44]: (k7_relat_1('#skF_5', B_44)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_44) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_62])).
% 1.96/1.19  tff(c_81, plain, (![B_44]: (k7_relat_1('#skF_5', B_44)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_44))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_77])).
% 1.96/1.19  tff(c_112, plain, (k7_relat_1('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_81])).
% 1.96/1.19  tff(c_136, plain, (![A_50, B_51, C_52, D_53]: (k5_relset_1(A_50, B_51, C_52, D_53)=k7_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.19  tff(c_139, plain, (![D_53]: (k5_relset_1('#skF_4', '#skF_2', '#skF_5', D_53)=k7_relat_1('#skF_5', D_53))), inference(resolution, [status(thm)], [c_26, c_136])).
% 1.96/1.19  tff(c_22, plain, (k5_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.96/1.19  tff(c_140, plain, (k7_relat_1('#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_139, c_22])).
% 1.96/1.19  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_140])).
% 1.96/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  Inference rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Ref     : 0
% 1.96/1.19  #Sup     : 26
% 1.96/1.19  #Fact    : 0
% 1.96/1.19  #Define  : 0
% 1.96/1.19  #Split   : 1
% 1.96/1.19  #Chain   : 0
% 1.96/1.19  #Close   : 0
% 1.96/1.19  
% 1.96/1.19  Ordering : KBO
% 1.96/1.19  
% 1.96/1.19  Simplification rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Subsume      : 1
% 1.96/1.19  #Demod        : 7
% 1.96/1.19  #Tautology    : 9
% 1.96/1.19  #SimpNegUnit  : 0
% 1.96/1.19  #BackRed      : 1
% 1.96/1.19  
% 1.96/1.19  #Partial instantiations: 0
% 1.96/1.19  #Strategies tried      : 1
% 1.96/1.19  
% 1.96/1.19  Timing (in seconds)
% 1.96/1.19  ----------------------
% 1.96/1.19  Preprocessing        : 0.29
% 1.96/1.19  Parsing              : 0.16
% 1.96/1.19  CNF conversion       : 0.02
% 1.96/1.19  Main loop            : 0.14
% 1.96/1.19  Inferencing          : 0.06
% 1.96/1.19  Reduction            : 0.04
% 1.96/1.19  Demodulation         : 0.03
% 1.96/1.19  BG Simplification    : 0.01
% 1.96/1.19  Subsumption          : 0.02
% 1.96/1.19  Abstraction          : 0.01
% 1.96/1.19  MUC search           : 0.00
% 1.96/1.19  Cooper               : 0.00
% 1.96/1.19  Total                : 0.46
% 1.96/1.19  Index Insertion      : 0.00
% 1.96/1.19  Index Deletion       : 0.00
% 1.96/1.19  Index Matching       : 0.00
% 1.96/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
