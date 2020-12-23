%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:29 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   82 ( 168 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(B,A)
                    & v3_pre_topc(C,A) )
                 => v3_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,u1_pre_topc(A_39))
      | ~ v3_pre_topc(B_38,A_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_87,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_81])).

tff(c_94,plain,(
    r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_87])).

tff(c_48,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_90,plain,
    ( r2_hidden('#skF_6',u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_97,plain,(
    r2_hidden('#skF_6',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_90])).

tff(c_332,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_89),B_90,C_91),u1_pre_topc(A_89))
      | ~ r2_hidden(C_91,u1_pre_topc(A_89))
      | ~ r2_hidden(B_90,u1_pre_topc(A_89))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ v2_pre_topc(A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_21] :
      ( m1_subset_1(u1_pre_topc(A_21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21))))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_61,plain,(
    ! [A_28,C_29,B_30] :
      ( m1_subset_1(A_28,C_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(C_29))
      | ~ r2_hidden(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_28,A_21] :
      ( m1_subset_1(A_28,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ r2_hidden(A_28,u1_pre_topc(A_21))
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_98,plain,(
    ! [B_40,A_41] :
      ( v3_pre_topc(B_40,A_41)
      | ~ r2_hidden(B_40,u1_pre_topc(A_41))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_108,plain,(
    ! [A_28,A_21] :
      ( v3_pre_topc(A_28,A_21)
      | ~ r2_hidden(A_28,u1_pre_topc(A_21))
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_68,c_98])).

tff(c_627,plain,(
    ! [A_139,B_140,C_141] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(A_139),B_140,C_141),A_139)
      | ~ r2_hidden(C_141,u1_pre_topc(A_139))
      | ~ r2_hidden(B_140,u1_pre_topc(A_139))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ v2_pre_topc(A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_332,c_108])).

tff(c_46,plain,(
    ~ v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_630,plain,
    ( ~ r2_hidden('#skF_6',u1_pre_topc('#skF_4'))
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_627,c_46])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_54,c_52,c_94,c_97,c_630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.58  
% 3.49/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.58  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 3.49/1.58  
% 3.49/1.58  %Foreground sorts:
% 3.49/1.58  
% 3.49/1.58  
% 3.49/1.58  %Background operators:
% 3.49/1.58  
% 3.49/1.58  
% 3.49/1.58  %Foreground operators:
% 3.49/1.58  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.49/1.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.49/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.49/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.58  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.49/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.49/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.58  
% 3.49/1.59  tff(f_86, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_pre_topc(C, A)) => v3_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_1)).
% 3.49/1.59  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.49/1.59  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 3.49/1.59  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.49/1.59  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.49/1.59  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.59  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.59  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.59  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.59  tff(c_50, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.59  tff(c_81, plain, (![B_38, A_39]: (r2_hidden(B_38, u1_pre_topc(A_39)) | ~v3_pre_topc(B_38, A_39) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.49/1.59  tff(c_87, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_81])).
% 3.49/1.59  tff(c_94, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_87])).
% 3.49/1.59  tff(c_48, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.59  tff(c_90, plain, (r2_hidden('#skF_6', u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_81])).
% 3.49/1.59  tff(c_97, plain, (r2_hidden('#skF_6', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_90])).
% 3.49/1.59  tff(c_332, plain, (![A_89, B_90, C_91]: (r2_hidden(k9_subset_1(u1_struct_0(A_89), B_90, C_91), u1_pre_topc(A_89)) | ~r2_hidden(C_91, u1_pre_topc(A_89)) | ~r2_hidden(B_90, u1_pre_topc(A_89)) | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~v2_pre_topc(A_89) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.49/1.59  tff(c_44, plain, (![A_21]: (m1_subset_1(u1_pre_topc(A_21), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21)))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.59  tff(c_61, plain, (![A_28, C_29, B_30]: (m1_subset_1(A_28, C_29) | ~m1_subset_1(B_30, k1_zfmisc_1(C_29)) | ~r2_hidden(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.59  tff(c_68, plain, (![A_28, A_21]: (m1_subset_1(A_28, k1_zfmisc_1(u1_struct_0(A_21))) | ~r2_hidden(A_28, u1_pre_topc(A_21)) | ~l1_pre_topc(A_21))), inference(resolution, [status(thm)], [c_44, c_61])).
% 3.49/1.59  tff(c_98, plain, (![B_40, A_41]: (v3_pre_topc(B_40, A_41) | ~r2_hidden(B_40, u1_pre_topc(A_41)) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.49/1.59  tff(c_108, plain, (![A_28, A_21]: (v3_pre_topc(A_28, A_21) | ~r2_hidden(A_28, u1_pre_topc(A_21)) | ~l1_pre_topc(A_21))), inference(resolution, [status(thm)], [c_68, c_98])).
% 3.49/1.59  tff(c_627, plain, (![A_139, B_140, C_141]: (v3_pre_topc(k9_subset_1(u1_struct_0(A_139), B_140, C_141), A_139) | ~r2_hidden(C_141, u1_pre_topc(A_139)) | ~r2_hidden(B_140, u1_pre_topc(A_139)) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~v2_pre_topc(A_139) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_332, c_108])).
% 3.49/1.59  tff(c_46, plain, (~v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.59  tff(c_630, plain, (~r2_hidden('#skF_6', u1_pre_topc('#skF_4')) | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_627, c_46])).
% 3.49/1.59  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_54, c_52, c_94, c_97, c_630])).
% 3.49/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.59  
% 3.49/1.59  Inference rules
% 3.49/1.59  ----------------------
% 3.49/1.59  #Ref     : 0
% 3.49/1.59  #Sup     : 111
% 3.49/1.59  #Fact    : 4
% 3.49/1.59  #Define  : 0
% 3.49/1.59  #Split   : 0
% 3.49/1.59  #Chain   : 0
% 3.49/1.59  #Close   : 0
% 3.49/1.59  
% 3.49/1.59  Ordering : KBO
% 3.49/1.59  
% 3.49/1.59  Simplification rules
% 3.49/1.59  ----------------------
% 3.49/1.59  #Subsume      : 13
% 3.49/1.59  #Demod        : 18
% 3.49/1.59  #Tautology    : 30
% 3.49/1.59  #SimpNegUnit  : 0
% 3.49/1.59  #BackRed      : 0
% 3.49/1.59  
% 3.49/1.59  #Partial instantiations: 0
% 3.49/1.59  #Strategies tried      : 1
% 3.49/1.59  
% 3.49/1.59  Timing (in seconds)
% 3.49/1.59  ----------------------
% 3.49/1.59  Preprocessing        : 0.32
% 3.49/1.59  Parsing              : 0.18
% 3.49/1.59  CNF conversion       : 0.02
% 3.49/1.59  Main loop            : 0.46
% 3.49/1.59  Inferencing          : 0.19
% 3.49/1.59  Reduction            : 0.10
% 3.49/1.59  Demodulation         : 0.07
% 3.49/1.59  BG Simplification    : 0.02
% 3.49/1.59  Subsumption          : 0.13
% 3.49/1.59  Abstraction          : 0.02
% 3.49/1.59  MUC search           : 0.00
% 3.49/1.59  Cooper               : 0.00
% 3.49/1.59  Total                : 0.81
% 3.49/1.59  Index Insertion      : 0.00
% 3.49/1.59  Index Deletion       : 0.00
% 3.49/1.59  Index Matching       : 0.00
% 3.49/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
