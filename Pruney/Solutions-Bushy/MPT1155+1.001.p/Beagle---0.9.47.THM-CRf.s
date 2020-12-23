%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1155+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:31 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 113 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 451 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_105,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ~ r2_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

tff(c_28,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_43,plain,(
    ! [A_34,B_35] :
      ( k2_orders_2(A_34,B_35) = a_2_1_orders_2(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_49,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_46])).

tff(c_50,plain,(
    k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_49])).

tff(c_20,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_51,plain,(
    r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_56,plain,(
    ! [A_36,B_37,C_38] :
      ( '#skF_1'(A_36,B_37,C_38) = A_36
      | ~ r2_hidden(A_36,a_2_1_orders_2(B_37,C_38))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(B_37)))
      | ~ l1_orders_2(B_37)
      | ~ v5_orders_2(B_37)
      | ~ v4_orders_2(B_37)
      | ~ v3_orders_2(B_37)
      | v2_struct_0(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_56])).

tff(c_61,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_24,c_58])).

tff(c_62,plain,(
    '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_61])).

tff(c_84,plain,(
    ! [B_52,A_53,C_54,E_55] :
      ( r2_orders_2(B_52,'#skF_1'(A_53,B_52,C_54),E_55)
      | ~ r2_hidden(E_55,C_54)
      | ~ m1_subset_1(E_55,u1_struct_0(B_52))
      | ~ r2_hidden(A_53,a_2_1_orders_2(B_52,C_54))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(B_52)))
      | ~ l1_orders_2(B_52)
      | ~ v5_orders_2(B_52)
      | ~ v4_orders_2(B_52)
      | ~ v3_orders_2(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_86,plain,(
    ! [A_53,E_55] :
      ( r2_orders_2('#skF_3','#skF_1'(A_53,'#skF_3','#skF_5'),E_55)
      | ~ r2_hidden(E_55,'#skF_5')
      | ~ m1_subset_1(E_55,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_53,a_2_1_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_84])).

tff(c_89,plain,(
    ! [A_53,E_55] :
      ( r2_orders_2('#skF_3','#skF_1'(A_53,'#skF_3','#skF_5'),E_55)
      | ~ r2_hidden(E_55,'#skF_5')
      | ~ m1_subset_1(E_55,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_53,a_2_1_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_86])).

tff(c_91,plain,(
    ! [A_56,E_57] :
      ( r2_orders_2('#skF_3','#skF_1'(A_56,'#skF_3','#skF_5'),E_57)
      | ~ r2_hidden(E_57,'#skF_5')
      | ~ m1_subset_1(E_57,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_56,a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_89])).

tff(c_100,plain,(
    ! [E_57] :
      ( r2_orders_2('#skF_3','#skF_4',E_57)
      | ~ r2_hidden(E_57,'#skF_5')
      | ~ m1_subset_1(E_57,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_110,plain,(
    ! [E_58] :
      ( r2_orders_2('#skF_3','#skF_4',E_58)
      | ~ r2_hidden(E_58,'#skF_5')
      | ~ m1_subset_1(E_58,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_100])).

tff(c_124,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_136,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_124])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r2_orders_2(A_17,B_18,B_18)
      | ~ m1_subset_1(C_19,u1_struct_0(A_17))
      | ~ m1_subset_1(B_18,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_139,plain,(
    ! [C_19] :
      ( ~ m1_subset_1(C_19,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_136,c_16])).

tff(c_142,plain,(
    ! [C_19] : ~ m1_subset_1(C_19,u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_139])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_26])).

%------------------------------------------------------------------------------
