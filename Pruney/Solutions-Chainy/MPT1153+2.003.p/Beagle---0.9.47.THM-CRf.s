%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:32 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 143 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 590 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r2_hidden(B,C)
                    & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_34,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_41,plain,(
    ! [A_34,B_35,C_36] :
      ( r3_orders_2(A_34,B_35,B_35)
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_43,plain,(
    ! [B_35] :
      ( r3_orders_2('#skF_3',B_35,B_35)
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_46,plain,(
    ! [B_35] :
      ( r3_orders_2('#skF_3',B_35,B_35)
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_43])).

tff(c_48,plain,(
    ! [B_37] :
      ( r3_orders_2('#skF_3',B_37,B_37)
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46])).

tff(c_51,plain,(
    r3_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_79,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_orders_2(A_47,B_48,C_49)
      | ~ r3_orders_2(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_47))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | ~ v3_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_81,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_79])).

tff(c_84,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_81])).

tff(c_85,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_84])).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_53,plain,(
    ! [A_41,B_42] :
      ( k1_orders_2(A_41,B_42) = a_2_0_orders_2(A_41,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_orders_2(A_41)
      | ~ v5_orders_2(A_41)
      | ~ v4_orders_2(A_41)
      | ~ v3_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_59,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_56])).

tff(c_60,plain,(
    k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_59])).

tff(c_24,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_61,plain,(
    r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24])).

tff(c_86,plain,(
    ! [A_50,B_51,C_52] :
      ( '#skF_1'(A_50,B_51,C_52) = A_50
      | ~ r2_hidden(A_50,a_2_0_orders_2(B_51,C_52))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(B_51)))
      | ~ l1_orders_2(B_51)
      | ~ v5_orders_2(B_51)
      | ~ v4_orders_2(B_51)
      | ~ v3_orders_2(B_51)
      | v2_struct_0(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_86])).

tff(c_91,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_88])).

tff(c_92,plain,(
    '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_91])).

tff(c_231,plain,(
    ! [B_82,E_83,A_84,C_85] :
      ( r2_orders_2(B_82,E_83,'#skF_1'(A_84,B_82,C_85))
      | ~ r2_hidden(E_83,C_85)
      | ~ m1_subset_1(E_83,u1_struct_0(B_82))
      | ~ r2_hidden(A_84,a_2_0_orders_2(B_82,C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(B_82)))
      | ~ l1_orders_2(B_82)
      | ~ v5_orders_2(B_82)
      | ~ v4_orders_2(B_82)
      | ~ v3_orders_2(B_82)
      | v2_struct_0(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_233,plain,(
    ! [E_83,A_84] :
      ( r2_orders_2('#skF_3',E_83,'#skF_1'(A_84,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_83,'#skF_5')
      | ~ m1_subset_1(E_83,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_84,a_2_0_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_236,plain,(
    ! [E_83,A_84] :
      ( r2_orders_2('#skF_3',E_83,'#skF_1'(A_84,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_83,'#skF_5')
      | ~ m1_subset_1(E_83,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_84,a_2_0_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_233])).

tff(c_238,plain,(
    ! [E_86,A_87] :
      ( r2_orders_2('#skF_3',E_86,'#skF_1'(A_87,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_86,'#skF_5')
      | ~ m1_subset_1(E_86,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_87,a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_236])).

tff(c_246,plain,(
    ! [E_86] :
      ( r2_orders_2('#skF_3',E_86,'#skF_4')
      | ~ r2_hidden(E_86,'#skF_5')
      | ~ m1_subset_1(E_86,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_238])).

tff(c_256,plain,(
    ! [E_88] :
      ( r2_orders_2('#skF_3',E_88,'#skF_4')
      | ~ r2_hidden(E_88,'#skF_5')
      | ~ m1_subset_1(E_88,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_246])).

tff(c_267,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_256])).

tff(c_278,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_267])).

tff(c_22,plain,(
    ! [A_23,C_29,B_27] :
      ( ~ r2_orders_2(A_23,C_29,B_27)
      | ~ r1_orders_2(A_23,B_27,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ m1_subset_1(B_27,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_280,plain,
    ( ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_22])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_85,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.33  
% 2.22/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.59/1.33  
% 2.59/1.33  %Foreground sorts:
% 2.59/1.33  
% 2.59/1.33  
% 2.59/1.33  %Background operators:
% 2.59/1.33  
% 2.59/1.33  
% 2.59/1.33  %Foreground operators:
% 2.59/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.33  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.59/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.33  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.59/1.33  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.59/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.33  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 2.59/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.33  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.59/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.59/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.33  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.59/1.33  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.59/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.59/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.33  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.59/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.33  
% 2.59/1.35  tff(f_134, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.59/1.35  tff(f_96, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.59/1.35  tff(f_83, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.59/1.35  tff(f_41, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 2.59/1.35  tff(f_68, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 2.59/1.35  tff(f_111, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 2.59/1.35  tff(c_34, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_32, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_38, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_41, plain, (![A_34, B_35, C_36]: (r3_orders_2(A_34, B_35, B_35) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | ~v3_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.59/1.35  tff(c_43, plain, (![B_35]: (r3_orders_2('#skF_3', B_35, B_35) | ~m1_subset_1(B_35, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.59/1.35  tff(c_46, plain, (![B_35]: (r3_orders_2('#skF_3', B_35, B_35) | ~m1_subset_1(B_35, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_43])).
% 2.59/1.35  tff(c_48, plain, (![B_37]: (r3_orders_2('#skF_3', B_37, B_37) | ~m1_subset_1(B_37, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_46])).
% 2.59/1.35  tff(c_51, plain, (r3_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_48])).
% 2.59/1.35  tff(c_79, plain, (![A_47, B_48, C_49]: (r1_orders_2(A_47, B_48, C_49) | ~r3_orders_2(A_47, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_47)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_orders_2(A_47) | ~v3_orders_2(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.59/1.35  tff(c_81, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_51, c_79])).
% 2.59/1.35  tff(c_84, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_81])).
% 2.59/1.35  tff(c_85, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_84])).
% 2.59/1.35  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_36, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_53, plain, (![A_41, B_42]: (k1_orders_2(A_41, B_42)=a_2_0_orders_2(A_41, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_orders_2(A_41) | ~v5_orders_2(A_41) | ~v4_orders_2(A_41) | ~v3_orders_2(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.35  tff(c_56, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_53])).
% 2.59/1.35  tff(c_59, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_56])).
% 2.59/1.35  tff(c_60, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_59])).
% 2.59/1.35  tff(c_24, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.59/1.35  tff(c_61, plain, (r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24])).
% 2.59/1.35  tff(c_86, plain, (![A_50, B_51, C_52]: ('#skF_1'(A_50, B_51, C_52)=A_50 | ~r2_hidden(A_50, a_2_0_orders_2(B_51, C_52)) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(B_51))) | ~l1_orders_2(B_51) | ~v5_orders_2(B_51) | ~v4_orders_2(B_51) | ~v3_orders_2(B_51) | v2_struct_0(B_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.59/1.35  tff(c_88, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_61, c_86])).
% 2.59/1.35  tff(c_91, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_88])).
% 2.59/1.35  tff(c_92, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_40, c_91])).
% 2.59/1.35  tff(c_231, plain, (![B_82, E_83, A_84, C_85]: (r2_orders_2(B_82, E_83, '#skF_1'(A_84, B_82, C_85)) | ~r2_hidden(E_83, C_85) | ~m1_subset_1(E_83, u1_struct_0(B_82)) | ~r2_hidden(A_84, a_2_0_orders_2(B_82, C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(B_82))) | ~l1_orders_2(B_82) | ~v5_orders_2(B_82) | ~v4_orders_2(B_82) | ~v3_orders_2(B_82) | v2_struct_0(B_82))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.59/1.35  tff(c_233, plain, (![E_83, A_84]: (r2_orders_2('#skF_3', E_83, '#skF_1'(A_84, '#skF_3', '#skF_5')) | ~r2_hidden(E_83, '#skF_5') | ~m1_subset_1(E_83, u1_struct_0('#skF_3')) | ~r2_hidden(A_84, a_2_0_orders_2('#skF_3', '#skF_5')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_231])).
% 2.59/1.35  tff(c_236, plain, (![E_83, A_84]: (r2_orders_2('#skF_3', E_83, '#skF_1'(A_84, '#skF_3', '#skF_5')) | ~r2_hidden(E_83, '#skF_5') | ~m1_subset_1(E_83, u1_struct_0('#skF_3')) | ~r2_hidden(A_84, a_2_0_orders_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_233])).
% 2.59/1.35  tff(c_238, plain, (![E_86, A_87]: (r2_orders_2('#skF_3', E_86, '#skF_1'(A_87, '#skF_3', '#skF_5')) | ~r2_hidden(E_86, '#skF_5') | ~m1_subset_1(E_86, u1_struct_0('#skF_3')) | ~r2_hidden(A_87, a_2_0_orders_2('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_236])).
% 2.59/1.35  tff(c_246, plain, (![E_86]: (r2_orders_2('#skF_3', E_86, '#skF_4') | ~r2_hidden(E_86, '#skF_5') | ~m1_subset_1(E_86, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_238])).
% 2.59/1.35  tff(c_256, plain, (![E_88]: (r2_orders_2('#skF_3', E_88, '#skF_4') | ~r2_hidden(E_88, '#skF_5') | ~m1_subset_1(E_88, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_246])).
% 2.59/1.35  tff(c_267, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_256])).
% 2.59/1.35  tff(c_278, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_267])).
% 2.59/1.35  tff(c_22, plain, (![A_23, C_29, B_27]: (~r2_orders_2(A_23, C_29, B_27) | ~r1_orders_2(A_23, B_27, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~m1_subset_1(B_27, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.59/1.35  tff(c_280, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_278, c_22])).
% 2.59/1.35  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_85, c_280])).
% 2.59/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  Inference rules
% 2.59/1.35  ----------------------
% 2.59/1.35  #Ref     : 0
% 2.59/1.35  #Sup     : 43
% 2.59/1.35  #Fact    : 0
% 2.59/1.35  #Define  : 0
% 2.59/1.35  #Split   : 0
% 2.59/1.35  #Chain   : 0
% 2.59/1.35  #Close   : 0
% 2.59/1.35  
% 2.59/1.35  Ordering : KBO
% 2.59/1.35  
% 2.59/1.35  Simplification rules
% 2.59/1.35  ----------------------
% 2.59/1.35  #Subsume      : 0
% 2.59/1.35  #Demod        : 108
% 2.59/1.35  #Tautology    : 14
% 2.59/1.35  #SimpNegUnit  : 20
% 2.59/1.35  #BackRed      : 1
% 2.59/1.35  
% 2.59/1.35  #Partial instantiations: 0
% 2.59/1.35  #Strategies tried      : 1
% 2.59/1.35  
% 2.59/1.35  Timing (in seconds)
% 2.59/1.35  ----------------------
% 2.59/1.35  Preprocessing        : 0.34
% 2.59/1.35  Parsing              : 0.18
% 2.59/1.35  CNF conversion       : 0.02
% 2.59/1.35  Main loop            : 0.24
% 2.59/1.35  Inferencing          : 0.09
% 2.59/1.35  Reduction            : 0.08
% 2.59/1.35  Demodulation         : 0.06
% 2.59/1.35  BG Simplification    : 0.02
% 2.59/1.35  Subsumption          : 0.04
% 2.59/1.35  Abstraction          : 0.01
% 2.59/1.35  MUC search           : 0.00
% 2.59/1.35  Cooper               : 0.00
% 2.59/1.35  Total                : 0.61
% 2.59/1.35  Index Insertion      : 0.00
% 2.59/1.35  Index Deletion       : 0.00
% 2.59/1.35  Index Matching       : 0.00
% 2.59/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
