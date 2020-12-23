%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1534+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:00 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   41 (  58 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 203 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( ( r1_lattice3(A,B,C)
                    & r1_orders_2(A,D,C) )
                 => r1_lattice3(A,B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_0)).

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

tff(f_57,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(c_16,plain,(
    r1_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    r1_orders_2('#skF_2','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( r2_hidden('#skF_1'(A_1,B_8,C_9),B_8)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_42,C_43,D_44,B_45] :
      ( r1_orders_2(A_42,C_43,D_44)
      | ~ r2_hidden(D_44,B_45)
      | ~ m1_subset_1(D_44,u1_struct_0(A_42))
      | ~ r1_lattice3(A_42,B_45,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_42))
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [B_52,C_51,A_55,C_53,A_54] :
      ( r1_orders_2(A_54,C_51,'#skF_1'(A_55,B_52,C_53))
      | ~ m1_subset_1('#skF_1'(A_55,B_52,C_53),u1_struct_0(A_54))
      | ~ r1_lattice3(A_54,B_52,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | r1_lattice3(A_55,B_52,C_53)
      | ~ m1_subset_1(C_53,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_61,plain,(
    ! [A_58,C_59,B_60,C_61] :
      ( r1_orders_2(A_58,C_59,'#skF_1'(A_58,B_60,C_61))
      | ~ r1_lattice3(A_58,B_60,C_59)
      | ~ m1_subset_1(C_59,u1_struct_0(A_58))
      | r1_lattice3(A_58,B_60,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_10,plain,(
    ! [A_13,B_21,D_27,C_25] :
      ( r1_orders_2(A_13,B_21,D_27)
      | ~ r1_orders_2(A_13,C_25,D_27)
      | ~ r1_orders_2(A_13,B_21,C_25)
      | ~ m1_subset_1(D_27,u1_struct_0(A_13))
      | ~ m1_subset_1(C_25,u1_struct_0(A_13))
      | ~ m1_subset_1(B_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v4_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ! [C_62,B_64,A_63,C_66,B_65] :
      ( r1_orders_2(A_63,B_65,'#skF_1'(A_63,B_64,C_62))
      | ~ r1_orders_2(A_63,B_65,C_66)
      | ~ m1_subset_1('#skF_1'(A_63,B_64,C_62),u1_struct_0(A_63))
      | ~ m1_subset_1(B_65,u1_struct_0(A_63))
      | ~ v4_orders_2(A_63)
      | ~ r1_lattice3(A_63,B_64,C_66)
      | ~ m1_subset_1(C_66,u1_struct_0(A_63))
      | r1_lattice3(A_63,B_64,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_61,c_10])).

tff(c_74,plain,(
    ! [B_64,C_62] :
      ( r1_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2',B_64,C_62))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_64,C_62),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ r1_lattice3('#skF_2',B_64,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | r1_lattice3('#skF_2',B_64,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_70])).

tff(c_79,plain,(
    ! [B_67,C_68] :
      ( r1_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2',B_67,C_68))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_67,C_68),u1_struct_0('#skF_2'))
      | ~ r1_lattice3('#skF_2',B_67,'#skF_4')
      | r1_lattice3('#skF_2',B_67,C_68)
      | ~ m1_subset_1(C_68,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_18,c_74])).

tff(c_83,plain,(
    ! [B_8,C_9] :
      ( r1_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2',B_8,C_9))
      | ~ r1_lattice3('#skF_2',B_8,'#skF_4')
      | r1_lattice3('#skF_2',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_87,plain,(
    ! [B_69,C_70] :
      ( r1_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2',B_69,C_70))
      | ~ r1_lattice3('#skF_2',B_69,'#skF_4')
      | r1_lattice3('#skF_2',B_69,C_70)
      | ~ m1_subset_1(C_70,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_83])).

tff(c_4,plain,(
    ! [A_1,C_9,B_8] :
      ( ~ r1_orders_2(A_1,C_9,'#skF_1'(A_1,B_8,C_9))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [B_69] :
      ( ~ l1_orders_2('#skF_2')
      | ~ r1_lattice3('#skF_2',B_69,'#skF_4')
      | r1_lattice3('#skF_2',B_69,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_105,plain,(
    ! [B_71] :
      ( ~ r1_lattice3('#skF_2',B_71,'#skF_4')
      | r1_lattice3('#skF_2',B_71,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22,c_95])).

tff(c_12,plain,(
    ~ r1_lattice3('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,(
    ~ r1_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_108])).

%------------------------------------------------------------------------------
