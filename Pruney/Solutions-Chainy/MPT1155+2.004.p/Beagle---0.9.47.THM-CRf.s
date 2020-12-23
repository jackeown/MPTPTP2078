%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:37 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 126 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 512 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(f_124,negated_conjecture,(
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
                    & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_101,axiom,(
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

tff(c_32,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,(
    ! [A_38,B_39] :
      ( r1_orders_2(A_38,B_39,B_39)
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_55,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_48])).

tff(c_56,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_55])).

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_59,plain,(
    ! [A_44,B_45] :
      ( k2_orders_2(A_44,B_45) = a_2_1_orders_2(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_65,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_62])).

tff(c_66,plain,(
    k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_65])).

tff(c_22,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_67,plain,(
    r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_22])).

tff(c_72,plain,(
    ! [A_46,B_47,C_48] :
      ( '#skF_1'(A_46,B_47,C_48) = A_46
      | ~ r2_hidden(A_46,a_2_1_orders_2(B_47,C_48))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(B_47)))
      | ~ l1_orders_2(B_47)
      | ~ v5_orders_2(B_47)
      | ~ v4_orders_2(B_47)
      | ~ v3_orders_2(B_47)
      | v2_struct_0(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_72])).

tff(c_77,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_26,c_74])).

tff(c_78,plain,(
    '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_77])).

tff(c_119,plain,(
    ! [B_65,A_66,C_67,E_68] :
      ( r2_orders_2(B_65,'#skF_1'(A_66,B_65,C_67),E_68)
      | ~ r2_hidden(E_68,C_67)
      | ~ m1_subset_1(E_68,u1_struct_0(B_65))
      | ~ r2_hidden(A_66,a_2_1_orders_2(B_65,C_67))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(B_65)))
      | ~ l1_orders_2(B_65)
      | ~ v5_orders_2(B_65)
      | ~ v4_orders_2(B_65)
      | ~ v3_orders_2(B_65)
      | v2_struct_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_121,plain,(
    ! [A_66,E_68] :
      ( r2_orders_2('#skF_3','#skF_1'(A_66,'#skF_3','#skF_5'),E_68)
      | ~ r2_hidden(E_68,'#skF_5')
      | ~ m1_subset_1(E_68,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,a_2_1_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_124,plain,(
    ! [A_66,E_68] :
      ( r2_orders_2('#skF_3','#skF_1'(A_66,'#skF_3','#skF_5'),E_68)
      | ~ r2_hidden(E_68,'#skF_5')
      | ~ m1_subset_1(E_68,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,a_2_1_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_121])).

tff(c_126,plain,(
    ! [A_69,E_70] :
      ( r2_orders_2('#skF_3','#skF_1'(A_69,'#skF_3','#skF_5'),E_70)
      | ~ r2_hidden(E_70,'#skF_5')
      | ~ m1_subset_1(E_70,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_69,a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_124])).

tff(c_134,plain,(
    ! [E_70] :
      ( r2_orders_2('#skF_3','#skF_4',E_70)
      | ~ r2_hidden(E_70,'#skF_5')
      | ~ m1_subset_1(E_70,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_126])).

tff(c_144,plain,(
    ! [E_71] :
      ( r2_orders_2('#skF_3','#skF_4',E_71)
      | ~ r2_hidden(E_71,'#skF_5')
      | ~ m1_subset_1(E_71,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_134])).

tff(c_158,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_170,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_158])).

tff(c_20,plain,(
    ! [A_23,C_29,B_27] :
      ( ~ r2_orders_2(A_23,C_29,B_27)
      | ~ r1_orders_2(A_23,B_27,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ m1_subset_1(B_27,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_176,plain,
    ( ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_20])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_56,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:09:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  
% 2.20/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.20/1.28  
% 2.20/1.28  %Foreground sorts:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Background operators:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Foreground operators:
% 2.20/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.20/1.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.20/1.28  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 2.20/1.28  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.20/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.20/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.20/1.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.20/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.28  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.20/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.28  
% 2.20/1.30  tff(f_124, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 2.20/1.30  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 2.20/1.30  tff(f_47, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 2.20/1.30  tff(f_74, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 2.20/1.30  tff(f_101, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 2.20/1.30  tff(c_32, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_30, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_36, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_44, plain, (![A_38, B_39]: (r1_orders_2(A_38, B_39, B_39) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | ~v3_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.30  tff(c_48, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_44])).
% 2.20/1.30  tff(c_55, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_48])).
% 2.20/1.30  tff(c_56, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_55])).
% 2.20/1.30  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_34, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_59, plain, (![A_44, B_45]: (k2_orders_2(A_44, B_45)=a_2_1_orders_2(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_orders_2(A_44) | ~v5_orders_2(A_44) | ~v4_orders_2(A_44) | ~v3_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.30  tff(c_62, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_59])).
% 2.20/1.30  tff(c_65, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_62])).
% 2.20/1.30  tff(c_66, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_65])).
% 2.20/1.30  tff(c_22, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.20/1.30  tff(c_67, plain, (r2_hidden('#skF_4', a_2_1_orders_2('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_22])).
% 2.20/1.30  tff(c_72, plain, (![A_46, B_47, C_48]: ('#skF_1'(A_46, B_47, C_48)=A_46 | ~r2_hidden(A_46, a_2_1_orders_2(B_47, C_48)) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(B_47))) | ~l1_orders_2(B_47) | ~v5_orders_2(B_47) | ~v4_orders_2(B_47) | ~v3_orders_2(B_47) | v2_struct_0(B_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.20/1.30  tff(c_74, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_67, c_72])).
% 2.20/1.30  tff(c_77, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_26, c_74])).
% 2.20/1.30  tff(c_78, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38, c_77])).
% 2.20/1.30  tff(c_119, plain, (![B_65, A_66, C_67, E_68]: (r2_orders_2(B_65, '#skF_1'(A_66, B_65, C_67), E_68) | ~r2_hidden(E_68, C_67) | ~m1_subset_1(E_68, u1_struct_0(B_65)) | ~r2_hidden(A_66, a_2_1_orders_2(B_65, C_67)) | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(B_65))) | ~l1_orders_2(B_65) | ~v5_orders_2(B_65) | ~v4_orders_2(B_65) | ~v3_orders_2(B_65) | v2_struct_0(B_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.20/1.30  tff(c_121, plain, (![A_66, E_68]: (r2_orders_2('#skF_3', '#skF_1'(A_66, '#skF_3', '#skF_5'), E_68) | ~r2_hidden(E_68, '#skF_5') | ~m1_subset_1(E_68, u1_struct_0('#skF_3')) | ~r2_hidden(A_66, a_2_1_orders_2('#skF_3', '#skF_5')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_119])).
% 2.20/1.30  tff(c_124, plain, (![A_66, E_68]: (r2_orders_2('#skF_3', '#skF_1'(A_66, '#skF_3', '#skF_5'), E_68) | ~r2_hidden(E_68, '#skF_5') | ~m1_subset_1(E_68, u1_struct_0('#skF_3')) | ~r2_hidden(A_66, a_2_1_orders_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_121])).
% 2.20/1.30  tff(c_126, plain, (![A_69, E_70]: (r2_orders_2('#skF_3', '#skF_1'(A_69, '#skF_3', '#skF_5'), E_70) | ~r2_hidden(E_70, '#skF_5') | ~m1_subset_1(E_70, u1_struct_0('#skF_3')) | ~r2_hidden(A_69, a_2_1_orders_2('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_38, c_124])).
% 2.20/1.30  tff(c_134, plain, (![E_70]: (r2_orders_2('#skF_3', '#skF_4', E_70) | ~r2_hidden(E_70, '#skF_5') | ~m1_subset_1(E_70, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', a_2_1_orders_2('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_126])).
% 2.20/1.30  tff(c_144, plain, (![E_71]: (r2_orders_2('#skF_3', '#skF_4', E_71) | ~r2_hidden(E_71, '#skF_5') | ~m1_subset_1(E_71, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_134])).
% 2.20/1.30  tff(c_158, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_144])).
% 2.20/1.30  tff(c_170, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_158])).
% 2.20/1.30  tff(c_20, plain, (![A_23, C_29, B_27]: (~r2_orders_2(A_23, C_29, B_27) | ~r1_orders_2(A_23, B_27, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~m1_subset_1(B_27, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.20/1.30  tff(c_176, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_170, c_20])).
% 2.20/1.30  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_56, c_176])).
% 2.20/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  Inference rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Ref     : 0
% 2.20/1.30  #Sup     : 25
% 2.20/1.30  #Fact    : 0
% 2.20/1.30  #Define  : 0
% 2.20/1.30  #Split   : 0
% 2.20/1.30  #Chain   : 0
% 2.20/1.30  #Close   : 0
% 2.20/1.30  
% 2.20/1.30  Ordering : KBO
% 2.20/1.30  
% 2.20/1.30  Simplification rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Subsume      : 0
% 2.20/1.30  #Demod        : 65
% 2.20/1.30  #Tautology    : 7
% 2.20/1.30  #SimpNegUnit  : 12
% 2.20/1.30  #BackRed      : 1
% 2.20/1.30  
% 2.20/1.30  #Partial instantiations: 0
% 2.20/1.30  #Strategies tried      : 1
% 2.20/1.30  
% 2.20/1.30  Timing (in seconds)
% 2.20/1.30  ----------------------
% 2.20/1.30  Preprocessing        : 0.33
% 2.42/1.30  Parsing              : 0.17
% 2.42/1.30  CNF conversion       : 0.02
% 2.42/1.30  Main loop            : 0.20
% 2.42/1.30  Inferencing          : 0.08
% 2.42/1.30  Reduction            : 0.07
% 2.42/1.30  Demodulation         : 0.05
% 2.42/1.30  BG Simplification    : 0.02
% 2.42/1.30  Subsumption          : 0.03
% 2.42/1.30  Abstraction          : 0.01
% 2.42/1.30  MUC search           : 0.00
% 2.42/1.30  Cooper               : 0.00
% 2.42/1.30  Total                : 0.56
% 2.42/1.30  Index Insertion      : 0.00
% 2.42/1.30  Index Deletion       : 0.00
% 2.42/1.30  Index Matching       : 0.00
% 2.42/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
