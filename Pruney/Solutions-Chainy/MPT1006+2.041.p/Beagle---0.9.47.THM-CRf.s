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
% DateTime   : Thu Dec  3 10:14:08 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 108 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 186 expanded)
%              Number of equality atoms :   15 (  55 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_mcart_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_18,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_31,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_67,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_40,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_31,c_67])).

tff(c_76,plain,(
    ! [A_41] : ~ r2_hidden(A_41,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_90,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_10])).

tff(c_84,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | A_14 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_18])).

tff(c_165,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( m1_subset_1(k8_relset_1(A_69,B_70,C_71,D_72),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_172,plain,(
    ! [A_74,B_73,C_77,D_76,A_75] :
      ( ~ v1_xboole_0(A_74)
      | ~ r2_hidden(A_75,k8_relset_1(A_74,B_73,C_77,D_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(resolution,[status(thm)],[c_165,c_14])).

tff(c_177,plain,(
    ! [A_78,C_79,B_80,D_81] :
      ( ~ v1_xboole_0(A_78)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_80)))
      | k8_relset_1(A_78,B_80,C_79,D_81) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_84,c_172])).

tff(c_192,plain,(
    ! [A_82,B_83,D_84] :
      ( ~ v1_xboole_0(A_82)
      | k8_relset_1(A_82,B_83,'#skF_4',D_84) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_88,c_177])).

tff(c_195,plain,(
    ! [B_83,D_84] : k8_relset_1('#skF_4',B_83,'#skF_4',D_84) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_90,c_192])).

tff(c_24,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_24])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_mcart_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.97/1.20  
% 1.97/1.20  %Foreground sorts:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Background operators:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Foreground operators:
% 1.97/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.20  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.97/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.97/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.97/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.20  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 1.97/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.20  
% 1.97/1.22  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 1.97/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.97/1.22  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.97/1.22  tff(f_76, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.97/1.22  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.97/1.22  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.97/1.22  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 1.97/1.22  tff(c_18, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.97/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.97/1.22  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.22  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.97/1.22  tff(c_31, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26])).
% 1.97/1.22  tff(c_67, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.22  tff(c_69, plain, (![A_40]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_40, '#skF_4'))), inference(resolution, [status(thm)], [c_31, c_67])).
% 1.97/1.22  tff(c_76, plain, (![A_41]: (~r2_hidden(A_41, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_69])).
% 1.97/1.22  tff(c_81, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_76])).
% 1.97/1.22  tff(c_90, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2])).
% 1.97/1.22  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.97/1.22  tff(c_88, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_10])).
% 1.97/1.22  tff(c_84, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | A_14='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_18])).
% 1.97/1.22  tff(c_165, plain, (![A_69, B_70, C_71, D_72]: (m1_subset_1(k8_relset_1(A_69, B_70, C_71, D_72), k1_zfmisc_1(A_69)) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.22  tff(c_14, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.22  tff(c_172, plain, (![A_74, B_73, C_77, D_76, A_75]: (~v1_xboole_0(A_74) | ~r2_hidden(A_75, k8_relset_1(A_74, B_73, C_77, D_76)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(resolution, [status(thm)], [c_165, c_14])).
% 1.97/1.22  tff(c_177, plain, (![A_78, C_79, B_80, D_81]: (~v1_xboole_0(A_78) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_80))) | k8_relset_1(A_78, B_80, C_79, D_81)='#skF_4')), inference(resolution, [status(thm)], [c_84, c_172])).
% 1.97/1.22  tff(c_192, plain, (![A_82, B_83, D_84]: (~v1_xboole_0(A_82) | k8_relset_1(A_82, B_83, '#skF_4', D_84)='#skF_4')), inference(resolution, [status(thm)], [c_88, c_177])).
% 1.97/1.22  tff(c_195, plain, (![B_83, D_84]: (k8_relset_1('#skF_4', B_83, '#skF_4', D_84)='#skF_4')), inference(resolution, [status(thm)], [c_90, c_192])).
% 1.97/1.22  tff(c_24, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.97/1.22  tff(c_83, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_24])).
% 1.97/1.22  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_83])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 36
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 0
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 5
% 1.97/1.22  #Demod        : 23
% 1.97/1.22  #Tautology    : 20
% 1.97/1.22  #SimpNegUnit  : 0
% 1.97/1.22  #BackRed      : 10
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.22  Preprocessing        : 0.29
% 1.97/1.22  Parsing              : 0.16
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.17
% 1.97/1.22  Inferencing          : 0.07
% 1.97/1.22  Reduction            : 0.05
% 1.97/1.22  Demodulation         : 0.04
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.03
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.49
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
