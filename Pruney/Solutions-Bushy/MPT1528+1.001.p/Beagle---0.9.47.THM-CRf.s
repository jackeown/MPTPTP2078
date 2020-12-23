%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1528+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:00 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(c_18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden('#skF_1'(A_44,B_45,C_46),B_45)
      | r1_lattice3(A_44,B_45,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [B_26,A_25] :
      ( ~ v1_xboole_0(B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [B_50,A_51,C_52] :
      ( ~ v1_xboole_0(B_50)
      | r1_lattice3(A_51,B_50,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(A_51))
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_62,c_20])).

tff(c_75,plain,(
    ! [B_50] :
      ( ~ v1_xboole_0(B_50)
      | r1_lattice3('#skF_3',B_50,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_80,plain,(
    ! [B_53] :
      ( ~ v1_xboole_0(B_53)
      | r1_lattice3('#skF_3',B_53,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75])).

tff(c_29,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_2'(A_30,B_31,C_32),B_31)
      | r2_lattice3(A_30,B_31,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [B_33,A_34,C_35] :
      ( ~ v1_xboole_0(B_33)
      | r2_lattice3(A_34,B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_29,c_20])).

tff(c_36,plain,(
    ! [B_33] :
      ( ~ v1_xboole_0(B_33)
      | r2_lattice3('#skF_3',B_33,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_40,plain,(
    ! [B_36] :
      ( ~ v1_xboole_0(B_36)
      | r2_lattice3('#skF_3',B_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_22,plain,
    ( ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_43,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_28])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_43])).

tff(c_48,plain,(
    ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_83,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_80,c_48])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_83])).

%------------------------------------------------------------------------------
