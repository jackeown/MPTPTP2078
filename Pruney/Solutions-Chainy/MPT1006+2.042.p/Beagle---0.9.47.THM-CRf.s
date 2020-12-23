%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:08 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 108 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 204 expanded)
%              Number of equality atoms :   14 (  49 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_20,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_29,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_65,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_44,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29,c_65])).

tff(c_74,plain,(
    ! [A_45] : ~ r2_hidden(A_45,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_79,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_88,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_10])).

tff(c_81,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | A_14 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_20])).

tff(c_151,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( m1_subset_1(k8_relset_1(A_55,B_56,C_57,D_58),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_164,plain,(
    ! [D_66,A_67,C_69,B_65,A_68] :
      ( ~ v1_xboole_0(A_67)
      | ~ r2_hidden(A_68,k8_relset_1(A_67,B_65,C_69,D_66))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_65))) ) ),
    inference(resolution,[status(thm)],[c_151,c_14])).

tff(c_169,plain,(
    ! [A_70,C_71,B_72,D_73] :
      ( ~ v1_xboole_0(A_70)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_70,B_72)))
      | k8_relset_1(A_70,B_72,C_71,D_73) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_81,c_164])).

tff(c_184,plain,(
    ! [A_74,B_75,D_76] :
      ( ~ v1_xboole_0(A_74)
      | k8_relset_1(A_74,B_75,'#skF_4',D_76) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_86,c_169])).

tff(c_187,plain,(
    ! [B_75,D_76] : k8_relset_1('#skF_4',B_75,'#skF_4',D_76) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_88,c_184])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_22])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:44:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.20  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.96/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.96/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.96/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.20  
% 1.96/1.22  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 1.96/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.96/1.22  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.96/1.22  tff(f_81, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.96/1.22  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.07/1.22  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.07/1.22  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.07/1.22  tff(c_20, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.07/1.22  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.22  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.07/1.22  tff(c_29, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 2.07/1.22  tff(c_65, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.22  tff(c_67, plain, (![A_44]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_44, '#skF_4'))), inference(resolution, [status(thm)], [c_29, c_65])).
% 2.07/1.22  tff(c_74, plain, (![A_45]: (~r2_hidden(A_45, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_67])).
% 2.07/1.22  tff(c_79, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20, c_74])).
% 2.07/1.22  tff(c_88, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_2])).
% 2.07/1.22  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.07/1.22  tff(c_86, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_10])).
% 2.07/1.22  tff(c_81, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | A_14='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_20])).
% 2.07/1.22  tff(c_151, plain, (![A_55, B_56, C_57, D_58]: (m1_subset_1(k8_relset_1(A_55, B_56, C_57, D_58), k1_zfmisc_1(A_55)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.22  tff(c_14, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.22  tff(c_164, plain, (![D_66, A_67, C_69, B_65, A_68]: (~v1_xboole_0(A_67) | ~r2_hidden(A_68, k8_relset_1(A_67, B_65, C_69, D_66)) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_65))))), inference(resolution, [status(thm)], [c_151, c_14])).
% 2.07/1.22  tff(c_169, plain, (![A_70, C_71, B_72, D_73]: (~v1_xboole_0(A_70) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_70, B_72))) | k8_relset_1(A_70, B_72, C_71, D_73)='#skF_4')), inference(resolution, [status(thm)], [c_81, c_164])).
% 2.07/1.22  tff(c_184, plain, (![A_74, B_75, D_76]: (~v1_xboole_0(A_74) | k8_relset_1(A_74, B_75, '#skF_4', D_76)='#skF_4')), inference(resolution, [status(thm)], [c_86, c_169])).
% 2.07/1.22  tff(c_187, plain, (![B_75, D_76]: (k8_relset_1('#skF_4', B_75, '#skF_4', D_76)='#skF_4')), inference(resolution, [status(thm)], [c_88, c_184])).
% 2.07/1.22  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.07/1.22  tff(c_82, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_22])).
% 2.07/1.22  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_82])).
% 2.07/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.22  
% 2.07/1.22  Inference rules
% 2.07/1.22  ----------------------
% 2.07/1.22  #Ref     : 0
% 2.07/1.22  #Sup     : 36
% 2.07/1.22  #Fact    : 0
% 2.07/1.22  #Define  : 0
% 2.07/1.22  #Split   : 0
% 2.07/1.22  #Chain   : 0
% 2.07/1.22  #Close   : 0
% 2.07/1.22  
% 2.07/1.22  Ordering : KBO
% 2.07/1.22  
% 2.07/1.22  Simplification rules
% 2.07/1.22  ----------------------
% 2.07/1.22  #Subsume      : 5
% 2.07/1.22  #Demod        : 22
% 2.07/1.22  #Tautology    : 20
% 2.07/1.22  #SimpNegUnit  : 0
% 2.07/1.22  #BackRed      : 10
% 2.07/1.22  
% 2.07/1.22  #Partial instantiations: 0
% 2.07/1.22  #Strategies tried      : 1
% 2.07/1.22  
% 2.07/1.22  Timing (in seconds)
% 2.07/1.22  ----------------------
% 2.07/1.22  Preprocessing        : 0.29
% 2.07/1.22  Parsing              : 0.17
% 2.07/1.22  CNF conversion       : 0.02
% 2.07/1.22  Main loop            : 0.18
% 2.07/1.22  Inferencing          : 0.07
% 2.07/1.22  Reduction            : 0.05
% 2.07/1.22  Demodulation         : 0.04
% 2.07/1.22  BG Simplification    : 0.01
% 2.07/1.22  Subsumption          : 0.03
% 2.07/1.22  Abstraction          : 0.01
% 2.07/1.22  MUC search           : 0.00
% 2.07/1.22  Cooper               : 0.00
% 2.07/1.22  Total                : 0.49
% 2.07/1.22  Index Insertion      : 0.00
% 2.07/1.22  Index Deletion       : 0.00
% 2.07/1.22  Index Matching       : 0.00
% 2.07/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
