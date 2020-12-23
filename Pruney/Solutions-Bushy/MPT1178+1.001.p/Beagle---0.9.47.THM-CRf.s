%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1178+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:32 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   57 (  77 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 185 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_47,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => m2_orders_2(k1_tarski(k1_funct_1(B,u1_struct_0(A))),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_orders_2)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_90,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_50,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20,plain,(
    ! [B_27,A_25] :
      ( m2_orders_2(k1_tarski(k1_funct_1(B_27,u1_struct_0(A_25))),A_25,B_27)
      | ~ m1_orders_1(B_27,k1_orders_1(u1_struct_0(A_25)))
      | ~ l1_orders_2(A_25)
      | ~ v5_orders_2(A_25)
      | ~ v4_orders_2(A_25)
      | ~ v3_orders_2(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_90,plain,(
    ! [D_44,A_45,B_46] :
      ( r2_hidden(D_44,k4_orders_2(A_45,B_46))
      | ~ m2_orders_2(D_44,A_45,B_46)
      | ~ m1_orders_1(B_46,k1_orders_1(u1_struct_0(A_45)))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_44,'#skF_4','#skF_5')
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_90])).

tff(c_95,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_44,'#skF_4','#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_92])).

tff(c_97,plain,(
    ! [D_47] :
      ( r2_hidden(D_47,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_47,'#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_95])).

tff(c_22,plain,(
    ! [A_28,B_31] :
      ( k3_tarski(A_28) != k1_xboole_0
      | ~ r2_hidden(B_31,A_28)
      | k1_xboole_0 = B_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102,plain,(
    ! [D_47] :
      ( k3_tarski(k4_orders_2('#skF_4','#skF_5')) != k1_xboole_0
      | k1_xboole_0 = D_47
      | ~ m2_orders_2(D_47,'#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_97,c_22])).

tff(c_110,plain,(
    ! [D_48] :
      ( k1_xboole_0 = D_48
      | ~ m2_orders_2(D_48,'#skF_4','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_102])).

tff(c_114,plain,
    ( k1_tarski(k1_funct_1('#skF_5',u1_struct_0('#skF_4'))) = k1_xboole_0
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_110])).

tff(c_117,plain,
    ( k1_tarski(k1_funct_1('#skF_5',u1_struct_0('#skF_4'))) = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_114])).

tff(c_118,plain,(
    k1_tarski(k1_funct_1('#skF_5',u1_struct_0('#skF_4'))) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_117])).

tff(c_16,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_tarski(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_16])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_124])).

%------------------------------------------------------------------------------
