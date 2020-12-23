%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1175+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:32 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 158 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_orders_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [B_10,A_6,C_12] :
      ( r2_hidden(k1_funct_1(B_10,u1_struct_0(A_6)),C_12)
      | ~ m2_orders_2(C_12,A_6,B_10)
      | ~ m1_orders_1(B_10,k1_orders_1(u1_struct_0(A_6)))
      | ~ l1_orders_2(A_6)
      | ~ v5_orders_2(A_6)
      | ~ v4_orders_2(A_6)
      | ~ v3_orders_2(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    ! [B_33,A_34,C_35] :
      ( r2_hidden(k1_funct_1(B_33,u1_struct_0(A_34)),C_35)
      | ~ m2_orders_2(C_35,A_34,B_33)
      | ~ m1_orders_1(B_33,k1_orders_1(u1_struct_0(A_34)))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_29,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,B_29)
      | ~ r2_hidden(C_30,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    ! [C_30] :
      ( ~ r2_hidden(C_30,'#skF_5')
      | ~ r2_hidden(C_30,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_29])).

tff(c_66,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(k1_funct_1(B_37,u1_struct_0(A_38)),'#skF_4')
      | ~ m2_orders_2('#skF_5',A_38,B_37)
      | ~ m1_orders_1(B_37,k1_orders_1(u1_struct_0(A_38)))
      | ~ l1_orders_2(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_53,c_32])).

tff(c_72,plain,(
    ! [A_39,B_40] :
      ( ~ m2_orders_2('#skF_5',A_39,B_40)
      | ~ m2_orders_2('#skF_4',A_39,B_40)
      | ~ m1_orders_1(B_40,k1_orders_1(u1_struct_0(A_39)))
      | ~ l1_orders_2(A_39)
      | ~ v5_orders_2(A_39)
      | ~ v4_orders_2(A_39)
      | ~ v3_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_75,plain,
    ( ~ m2_orders_2('#skF_5','#skF_2','#skF_3')
    | ~ m2_orders_2('#skF_4','#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_78,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_14,c_12,c_75])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_78])).

%------------------------------------------------------------------------------
