%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:37 EST 2020

% Result     : Theorem 2.32s
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
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_140,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

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

tff(f_117,axiom,(
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

tff(c_36,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_34,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_48,plain,(
    ! [A_41,B_42,C_43] :
      ( r3_orders_2(A_41,B_42,B_42)
      | ~ m1_subset_1(C_43,u1_struct_0(A_41))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41)
      | ~ v3_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ! [B_42] :
      ( r3_orders_2('#skF_3',B_42,B_42)
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_59,plain,(
    ! [B_42] :
      ( r3_orders_2('#skF_3',B_42,B_42)
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_52])).

tff(c_61,plain,(
    ! [B_44] :
      ( r3_orders_2('#skF_3',B_44,B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_59])).

tff(c_67,plain,(
    r3_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_61])).

tff(c_115,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_orders_2(A_59,B_60,C_61)
      | ~ r3_orders_2(A_59,B_60,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_123,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_115])).

tff(c_138,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_32,c_123])).

tff(c_139,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_138])).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_38,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_70,plain,(
    ! [A_49,B_50] :
      ( k2_orders_2(A_49,B_50) = a_2_1_orders_2(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_76,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_73])).

tff(c_77,plain,(
    k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_76])).

tff(c_26,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_78,plain,(
    r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_26])).

tff(c_157,plain,(
    ! [A_66,B_67,C_68] :
      ( '#skF_1'(A_66,B_67,C_68) = A_66
      | ~ r2_hidden(A_66,a_2_1_orders_2(B_67,C_68))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(B_67)))
      | ~ l1_orders_2(B_67)
      | ~ v5_orders_2(B_67)
      | ~ v4_orders_2(B_67)
      | ~ v3_orders_2(B_67)
      | v2_struct_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_159,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_157])).

tff(c_162,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_30,c_159])).

tff(c_163,plain,(
    '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_162])).

tff(c_327,plain,(
    ! [B_100,A_101,C_102,E_103] :
      ( r2_orders_2(B_100,'#skF_1'(A_101,B_100,C_102),E_103)
      | ~ r2_hidden(E_103,C_102)
      | ~ m1_subset_1(E_103,u1_struct_0(B_100))
      | ~ r2_hidden(A_101,a_2_1_orders_2(B_100,C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(B_100)))
      | ~ l1_orders_2(B_100)
      | ~ v5_orders_2(B_100)
      | ~ v4_orders_2(B_100)
      | ~ v3_orders_2(B_100)
      | v2_struct_0(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_329,plain,(
    ! [A_101,E_103] :
      ( r2_orders_2('#skF_3','#skF_1'(A_101,'#skF_3','#skF_5'),E_103)
      | ~ r2_hidden(E_103,'#skF_5')
      | ~ m1_subset_1(E_103,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_101,a_2_1_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_327])).

tff(c_332,plain,(
    ! [A_101,E_103] :
      ( r2_orders_2('#skF_3','#skF_1'(A_101,'#skF_3','#skF_5'),E_103)
      | ~ r2_hidden(E_103,'#skF_5')
      | ~ m1_subset_1(E_103,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_101,a_2_1_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_329])).

tff(c_334,plain,(
    ! [A_104,E_105] :
      ( r2_orders_2('#skF_3','#skF_1'(A_104,'#skF_3','#skF_5'),E_105)
      | ~ r2_hidden(E_105,'#skF_5')
      | ~ m1_subset_1(E_105,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_104,a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_332])).

tff(c_342,plain,(
    ! [E_105] :
      ( r2_orders_2('#skF_3','#skF_4',E_105)
      | ~ r2_hidden(E_105,'#skF_5')
      | ~ m1_subset_1(E_105,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_334])).

tff(c_352,plain,(
    ! [E_106] :
      ( r2_orders_2('#skF_3','#skF_4',E_106)
      | ~ r2_hidden(E_106,'#skF_5')
      | ~ m1_subset_1(E_106,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_342])).

tff(c_366,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_352])).

tff(c_378,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_366])).

tff(c_24,plain,(
    ! [A_26,C_32,B_30] :
      ( ~ r2_orders_2(A_26,C_32,B_30)
      | ~ r1_orders_2(A_26,B_30,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l1_orders_2(A_26)
      | ~ v5_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_380,plain,
    ( ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_24])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_139,c_380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.31  
% 2.59/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.31  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.59/1.31  
% 2.59/1.31  %Foreground sorts:
% 2.59/1.31  
% 2.59/1.31  
% 2.59/1.31  %Background operators:
% 2.59/1.31  
% 2.59/1.31  
% 2.59/1.31  %Foreground operators:
% 2.59/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.31  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.59/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.59/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.31  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.59/1.31  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 2.59/1.31  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.59/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.59/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.59/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.59/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.59/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.31  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.59/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.31  
% 2.59/1.33  tff(f_140, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 2.59/1.33  tff(f_102, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.59/1.33  tff(f_89, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.59/1.33  tff(f_47, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 2.59/1.33  tff(f_74, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 2.59/1.33  tff(f_117, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 2.59/1.33  tff(c_36, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_34, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_40, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_48, plain, (![A_41, B_42, C_43]: (r3_orders_2(A_41, B_42, B_42) | ~m1_subset_1(C_43, u1_struct_0(A_41)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_orders_2(A_41) | ~v3_orders_2(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.59/1.33  tff(c_52, plain, (![B_42]: (r3_orders_2('#skF_3', B_42, B_42) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.59/1.33  tff(c_59, plain, (![B_42]: (r3_orders_2('#skF_3', B_42, B_42) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_52])).
% 2.59/1.33  tff(c_61, plain, (![B_44]: (r3_orders_2('#skF_3', B_44, B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_59])).
% 2.59/1.33  tff(c_67, plain, (r3_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_61])).
% 2.59/1.33  tff(c_115, plain, (![A_59, B_60, C_61]: (r1_orders_2(A_59, B_60, C_61) | ~r3_orders_2(A_59, B_60, C_61) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.59/1.33  tff(c_123, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_67, c_115])).
% 2.59/1.33  tff(c_138, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_32, c_123])).
% 2.59/1.33  tff(c_139, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_138])).
% 2.59/1.33  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_38, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_70, plain, (![A_49, B_50]: (k2_orders_2(A_49, B_50)=a_2_1_orders_2(A_49, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.59/1.33  tff(c_73, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_70])).
% 2.59/1.33  tff(c_76, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_73])).
% 2.59/1.33  tff(c_77, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_76])).
% 2.59/1.33  tff(c_26, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.59/1.33  tff(c_78, plain, (r2_hidden('#skF_4', a_2_1_orders_2('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_26])).
% 2.59/1.33  tff(c_157, plain, (![A_66, B_67, C_68]: ('#skF_1'(A_66, B_67, C_68)=A_66 | ~r2_hidden(A_66, a_2_1_orders_2(B_67, C_68)) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(B_67))) | ~l1_orders_2(B_67) | ~v5_orders_2(B_67) | ~v4_orders_2(B_67) | ~v3_orders_2(B_67) | v2_struct_0(B_67))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.33  tff(c_159, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_157])).
% 2.59/1.33  tff(c_162, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_30, c_159])).
% 2.59/1.33  tff(c_163, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_42, c_162])).
% 2.59/1.33  tff(c_327, plain, (![B_100, A_101, C_102, E_103]: (r2_orders_2(B_100, '#skF_1'(A_101, B_100, C_102), E_103) | ~r2_hidden(E_103, C_102) | ~m1_subset_1(E_103, u1_struct_0(B_100)) | ~r2_hidden(A_101, a_2_1_orders_2(B_100, C_102)) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(B_100))) | ~l1_orders_2(B_100) | ~v5_orders_2(B_100) | ~v4_orders_2(B_100) | ~v3_orders_2(B_100) | v2_struct_0(B_100))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.33  tff(c_329, plain, (![A_101, E_103]: (r2_orders_2('#skF_3', '#skF_1'(A_101, '#skF_3', '#skF_5'), E_103) | ~r2_hidden(E_103, '#skF_5') | ~m1_subset_1(E_103, u1_struct_0('#skF_3')) | ~r2_hidden(A_101, a_2_1_orders_2('#skF_3', '#skF_5')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_327])).
% 2.59/1.33  tff(c_332, plain, (![A_101, E_103]: (r2_orders_2('#skF_3', '#skF_1'(A_101, '#skF_3', '#skF_5'), E_103) | ~r2_hidden(E_103, '#skF_5') | ~m1_subset_1(E_103, u1_struct_0('#skF_3')) | ~r2_hidden(A_101, a_2_1_orders_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_329])).
% 2.59/1.33  tff(c_334, plain, (![A_104, E_105]: (r2_orders_2('#skF_3', '#skF_1'(A_104, '#skF_3', '#skF_5'), E_105) | ~r2_hidden(E_105, '#skF_5') | ~m1_subset_1(E_105, u1_struct_0('#skF_3')) | ~r2_hidden(A_104, a_2_1_orders_2('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_42, c_332])).
% 2.59/1.33  tff(c_342, plain, (![E_105]: (r2_orders_2('#skF_3', '#skF_4', E_105) | ~r2_hidden(E_105, '#skF_5') | ~m1_subset_1(E_105, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', a_2_1_orders_2('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_334])).
% 2.59/1.33  tff(c_352, plain, (![E_106]: (r2_orders_2('#skF_3', '#skF_4', E_106) | ~r2_hidden(E_106, '#skF_5') | ~m1_subset_1(E_106, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_342])).
% 2.59/1.33  tff(c_366, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_352])).
% 2.59/1.33  tff(c_378, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_366])).
% 2.59/1.33  tff(c_24, plain, (![A_26, C_32, B_30]: (~r2_orders_2(A_26, C_32, B_30) | ~r1_orders_2(A_26, B_30, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~m1_subset_1(B_30, u1_struct_0(A_26)) | ~l1_orders_2(A_26) | ~v5_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.59/1.33  tff(c_380, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_378, c_24])).
% 2.59/1.33  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_139, c_380])).
% 2.59/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  
% 2.59/1.33  Inference rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Ref     : 0
% 2.59/1.33  #Sup     : 61
% 2.59/1.33  #Fact    : 0
% 2.59/1.33  #Define  : 0
% 2.59/1.33  #Split   : 0
% 2.59/1.33  #Chain   : 0
% 2.59/1.33  #Close   : 0
% 2.59/1.33  
% 2.59/1.33  Ordering : KBO
% 2.59/1.33  
% 2.59/1.33  Simplification rules
% 2.59/1.33  ----------------------
% 2.59/1.33  #Subsume      : 4
% 2.59/1.33  #Demod        : 137
% 2.59/1.33  #Tautology    : 18
% 2.59/1.33  #SimpNegUnit  : 29
% 2.59/1.33  #BackRed      : 1
% 2.59/1.33  
% 2.59/1.33  #Partial instantiations: 0
% 2.59/1.33  #Strategies tried      : 1
% 2.59/1.33  
% 2.59/1.33  Timing (in seconds)
% 2.59/1.33  ----------------------
% 2.59/1.33  Preprocessing        : 0.31
% 2.59/1.33  Parsing              : 0.16
% 2.59/1.33  CNF conversion       : 0.02
% 2.59/1.33  Main loop            : 0.26
% 2.59/1.33  Inferencing          : 0.10
% 2.59/1.33  Reduction            : 0.08
% 2.59/1.33  Demodulation         : 0.06
% 2.59/1.33  BG Simplification    : 0.02
% 2.59/1.33  Subsumption          : 0.05
% 2.59/1.33  Abstraction          : 0.01
% 2.59/1.33  MUC search           : 0.00
% 2.59/1.33  Cooper               : 0.00
% 2.59/1.33  Total                : 0.61
% 2.59/1.33  Index Insertion      : 0.00
% 2.59/1.33  Index Deletion       : 0.00
% 2.59/1.33  Index Matching       : 0.00
% 2.59/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
