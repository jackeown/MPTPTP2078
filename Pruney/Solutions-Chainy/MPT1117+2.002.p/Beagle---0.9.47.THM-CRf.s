%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:02 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   50 (  94 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 222 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( r2_hidden(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( v4_pre_topc(D,A)
                        & r1_tarski(B,D) )
                     => r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_1'(A_37,B_38),B_38)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_45,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_43,B_44,B_45] :
      ( r2_hidden('#skF_1'(A_43,B_44),B_45)
      | ~ r1_tarski(A_43,B_45)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_46,B_47,B_48,B_49] :
      ( r2_hidden('#skF_1'(A_46,B_47),B_48)
      | ~ r1_tarski(B_49,B_48)
      | ~ r1_tarski(A_46,B_49)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_65,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_50,'#skF_4')
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_72,plain,(
    ! [A_50,B_51,B_2] :
      ( r2_hidden('#skF_1'(A_50,B_51),B_2)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_2)
      | ~ r1_tarski(A_50,'#skF_4')
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_26,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_46,'#skF_4')
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_87,plain,(
    ! [B_56,A_57,C_58] :
      ( r1_tarski(B_56,'#skF_2'(A_57,B_56,C_58))
      | r2_hidden(C_58,k2_pre_topc(A_57,B_56))
      | ~ r2_hidden(C_58,u1_struct_0(A_57))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [C_58] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4',C_58))
      | r2_hidden(C_58,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden(C_58,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_106,plain,(
    ! [C_61] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4',C_61))
      | r2_hidden(C_61,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden(C_61,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_92])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_192,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4','#skF_1'(A_84,k2_pre_topc('#skF_3','#skF_4'))))
      | ~ r2_hidden('#skF_1'(A_84,k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_215,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4','#skF_1'(A_85,k2_pre_topc('#skF_3','#skF_4'))))
      | ~ r1_tarski(A_85,'#skF_4')
      | r1_tarski(A_85,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_192])).

tff(c_56,plain,(
    ! [A_43,B_44,B_2,B_45] :
      ( r2_hidden('#skF_1'(A_43,B_44),B_2)
      | ~ r1_tarski(B_45,B_2)
      | ~ r1_tarski(A_43,B_45)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_313,plain,(
    ! [A_93,B_94,A_95] :
      ( r2_hidden('#skF_1'(A_93,B_94),'#skF_2'('#skF_3','#skF_4','#skF_1'(A_95,k2_pre_topc('#skF_3','#skF_4'))))
      | ~ r1_tarski(A_93,'#skF_4')
      | r1_tarski(A_93,B_94)
      | ~ r1_tarski(A_95,'#skF_4')
      | r1_tarski(A_95,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_215,c_56])).

tff(c_14,plain,(
    ! [C_26,A_8,B_20] :
      ( ~ r2_hidden(C_26,'#skF_2'(A_8,B_20,C_26))
      | r2_hidden(C_26,k2_pre_topc(A_8,B_20))
      | ~ r2_hidden(C_26,u1_struct_0(A_8))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_316,plain,(
    ! [A_95] :
      ( r2_hidden('#skF_1'(A_95,k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_95,k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_95,'#skF_4')
      | r1_tarski(A_95,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_313,c_14])).

tff(c_530,plain,(
    ! [A_124] :
      ( r2_hidden('#skF_1'(A_124,k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_124,k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_124,'#skF_4')
      | r1_tarski(A_124,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_316])).

tff(c_544,plain,(
    ! [A_129] :
      ( ~ r2_hidden('#skF_1'(A_129,k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_129,'#skF_4')
      | r1_tarski(A_129,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_530,c_4])).

tff(c_548,plain,(
    ! [A_50] :
      ( ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_50,'#skF_4')
      | r1_tarski(A_50,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_72,c_544])).

tff(c_568,plain,(
    ! [A_130] :
      ( ~ r1_tarski(A_130,'#skF_4')
      | r1_tarski(A_130,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_548])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_596,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_568,c_22])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.51  
% 3.05/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.51  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.05/1.51  
% 3.05/1.51  %Foreground sorts:
% 3.05/1.51  
% 3.05/1.51  
% 3.05/1.51  %Background operators:
% 3.05/1.51  
% 3.05/1.51  
% 3.05/1.51  %Foreground operators:
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.05/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.05/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.05/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.51  
% 3.29/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.29/1.53  tff(f_63, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.29/1.53  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.29/1.53  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (r2_hidden(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(D, A) & r1_tarski(B, D)) => r2_hidden(C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_pre_topc)).
% 3.29/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_38, plain, (![A_37, B_38]: (~r2_hidden('#skF_1'(A_37, B_38), B_38) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_43, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_38])).
% 3.29/1.53  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.53  tff(c_28, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.29/1.53  tff(c_36, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_28])).
% 3.29/1.53  tff(c_45, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_49, plain, (![A_43, B_44, B_45]: (r2_hidden('#skF_1'(A_43, B_44), B_45) | ~r1_tarski(A_43, B_45) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_6, c_45])).
% 3.29/1.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_58, plain, (![A_46, B_47, B_48, B_49]: (r2_hidden('#skF_1'(A_46, B_47), B_48) | ~r1_tarski(B_49, B_48) | ~r1_tarski(A_46, B_49) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_49, c_2])).
% 3.29/1.53  tff(c_65, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), u1_struct_0('#skF_3')) | ~r1_tarski(A_50, '#skF_4') | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_36, c_58])).
% 3.29/1.53  tff(c_72, plain, (![A_50, B_51, B_2]: (r2_hidden('#skF_1'(A_50, B_51), B_2) | ~r1_tarski(u1_struct_0('#skF_3'), B_2) | ~r1_tarski(A_50, '#skF_4') | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_65, c_2])).
% 3.29/1.53  tff(c_26, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.53  tff(c_64, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), u1_struct_0('#skF_3')) | ~r1_tarski(A_46, '#skF_4') | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_36, c_58])).
% 3.29/1.53  tff(c_87, plain, (![B_56, A_57, C_58]: (r1_tarski(B_56, '#skF_2'(A_57, B_56, C_58)) | r2_hidden(C_58, k2_pre_topc(A_57, B_56)) | ~r2_hidden(C_58, u1_struct_0(A_57)) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.53  tff(c_92, plain, (![C_58]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', C_58)) | r2_hidden(C_58, k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden(C_58, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_87])).
% 3.29/1.53  tff(c_106, plain, (![C_61]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', C_61)) | r2_hidden(C_61, k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden(C_61, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_92])).
% 3.29/1.53  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_192, plain, (![A_84]: (r1_tarski(A_84, k2_pre_topc('#skF_3', '#skF_4')) | r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_1'(A_84, k2_pre_topc('#skF_3', '#skF_4')))) | ~r2_hidden('#skF_1'(A_84, k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_106, c_4])).
% 3.29/1.53  tff(c_215, plain, (![A_85]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_1'(A_85, k2_pre_topc('#skF_3', '#skF_4')))) | ~r1_tarski(A_85, '#skF_4') | r1_tarski(A_85, k2_pre_topc('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_64, c_192])).
% 3.29/1.53  tff(c_56, plain, (![A_43, B_44, B_2, B_45]: (r2_hidden('#skF_1'(A_43, B_44), B_2) | ~r1_tarski(B_45, B_2) | ~r1_tarski(A_43, B_45) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_49, c_2])).
% 3.29/1.53  tff(c_313, plain, (![A_93, B_94, A_95]: (r2_hidden('#skF_1'(A_93, B_94), '#skF_2'('#skF_3', '#skF_4', '#skF_1'(A_95, k2_pre_topc('#skF_3', '#skF_4')))) | ~r1_tarski(A_93, '#skF_4') | r1_tarski(A_93, B_94) | ~r1_tarski(A_95, '#skF_4') | r1_tarski(A_95, k2_pre_topc('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_215, c_56])).
% 3.29/1.53  tff(c_14, plain, (![C_26, A_8, B_20]: (~r2_hidden(C_26, '#skF_2'(A_8, B_20, C_26)) | r2_hidden(C_26, k2_pre_topc(A_8, B_20)) | ~r2_hidden(C_26, u1_struct_0(A_8)) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.53  tff(c_316, plain, (![A_95]: (r2_hidden('#skF_1'(A_95, k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_95, k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_95, '#skF_4') | r1_tarski(A_95, k2_pre_topc('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_313, c_14])).
% 3.29/1.53  tff(c_530, plain, (![A_124]: (r2_hidden('#skF_1'(A_124, k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_124, k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~r1_tarski(A_124, '#skF_4') | r1_tarski(A_124, k2_pre_topc('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_316])).
% 3.29/1.53  tff(c_544, plain, (![A_129]: (~r2_hidden('#skF_1'(A_129, k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~r1_tarski(A_129, '#skF_4') | r1_tarski(A_129, k2_pre_topc('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_530, c_4])).
% 3.29/1.53  tff(c_548, plain, (![A_50]: (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~r1_tarski(A_50, '#skF_4') | r1_tarski(A_50, k2_pre_topc('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_72, c_544])).
% 3.29/1.53  tff(c_568, plain, (![A_130]: (~r1_tarski(A_130, '#skF_4') | r1_tarski(A_130, k2_pre_topc('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_548])).
% 3.29/1.53  tff(c_22, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.53  tff(c_596, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_568, c_22])).
% 3.29/1.53  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_596])).
% 3.29/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  Inference rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Ref     : 0
% 3.29/1.53  #Sup     : 142
% 3.29/1.53  #Fact    : 0
% 3.29/1.53  #Define  : 0
% 3.29/1.53  #Split   : 4
% 3.29/1.53  #Chain   : 0
% 3.29/1.53  #Close   : 0
% 3.29/1.53  
% 3.29/1.53  Ordering : KBO
% 3.29/1.53  
% 3.29/1.53  Simplification rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Subsume      : 52
% 3.29/1.53  #Demod        : 18
% 3.29/1.53  #Tautology    : 3
% 3.29/1.53  #SimpNegUnit  : 2
% 3.29/1.53  #BackRed      : 0
% 3.29/1.53  
% 3.29/1.53  #Partial instantiations: 0
% 3.29/1.53  #Strategies tried      : 1
% 3.29/1.53  
% 3.29/1.53  Timing (in seconds)
% 3.29/1.53  ----------------------
% 3.29/1.53  Preprocessing        : 0.29
% 3.29/1.53  Parsing              : 0.16
% 3.29/1.53  CNF conversion       : 0.02
% 3.29/1.53  Main loop            : 0.41
% 3.29/1.53  Inferencing          : 0.15
% 3.29/1.53  Reduction            : 0.10
% 3.29/1.53  Demodulation         : 0.07
% 3.29/1.53  BG Simplification    : 0.02
% 3.29/1.53  Subsumption          : 0.12
% 3.29/1.53  Abstraction          : 0.02
% 3.29/1.53  MUC search           : 0.00
% 3.29/1.53  Cooper               : 0.00
% 3.29/1.53  Total                : 0.73
% 3.29/1.53  Index Insertion      : 0.00
% 3.29/1.53  Index Deletion       : 0.00
% 3.29/1.53  Index Matching       : 0.00
% 3.29/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
