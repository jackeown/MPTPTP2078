%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1195+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:34 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  119 ( 326 expanded)
%              Number of equality atoms :   30 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v8_lattices(A)
          & v9_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_lattices(A,B,C)
                <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_75,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_39,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(c_38,plain,
    ( k2_lattices('#skF_5','#skF_6','#skF_7') != '#skF_6'
    | ~ r1_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_55,plain,(
    ~ r1_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_36] :
      ( l2_lattices(A_36)
      | ~ l3_lattices(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    l2_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_67,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_lattices(A_43,B_44,C_45)
      | k1_lattices(A_43,B_44,C_45) != C_45
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l2_lattices(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [B_44] :
      ( r1_lattices('#skF_5',B_44,'#skF_7')
      | k1_lattices('#skF_5',B_44,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_90,plain,(
    ! [B_44] :
      ( r1_lattices('#skF_5',B_44,'#skF_7')
      | k1_lattices('#skF_5',B_44,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_79])).

tff(c_136,plain,(
    ! [B_50] :
      ( r1_lattices('#skF_5',B_50,'#skF_7')
      | k1_lattices('#skF_5',B_50,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_90])).

tff(c_155,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_7')
    | k1_lattices('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_136])).

tff(c_177,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_155])).

tff(c_44,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_7')
    | k2_lattices('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_56,plain,(
    k2_lattices('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_44])).

tff(c_34,plain,(
    v8_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_283,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_lattices(A_56,k2_lattices(A_56,B_57,C_58),C_58) = C_58
      | ~ m1_subset_1(C_58,u1_struct_0(A_56))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ v8_lattices(A_56)
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_295,plain,(
    ! [B_57] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_57,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_283])).

tff(c_306,plain,(
    ! [B_57] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_57,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_295])).

tff(c_365,plain,(
    ! [B_60] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_60,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_306])).

tff(c_384,plain,(
    k1_lattices('#skF_5',k2_lattices('#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_365])).

tff(c_405,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_384])).

tff(c_407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_405])).

tff(c_408,plain,(
    k2_lattices('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_409,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_418,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_lattices(A_67,B_68,C_69) = C_69
      | ~ r1_lattices(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l2_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_420,plain,
    ( k1_lattices('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l2_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_409,c_418])).

tff(c_423,plain,
    ( k1_lattices('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_28,c_26,c_420])).

tff(c_424,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_423])).

tff(c_32,plain,(
    v9_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_619,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_lattices(A_79,B_80,k1_lattices(A_79,B_80,C_81)) = B_80
      | ~ m1_subset_1(C_81,u1_struct_0(A_79))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ v9_lattices(A_79)
      | ~ l3_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_631,plain,(
    ! [B_80] :
      ( k2_lattices('#skF_5',B_80,k1_lattices('#skF_5',B_80,'#skF_7')) = B_80
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_619])).

tff(c_642,plain,(
    ! [B_80] :
      ( k2_lattices('#skF_5',B_80,k1_lattices('#skF_5',B_80,'#skF_7')) = B_80
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_631])).

tff(c_688,plain,(
    ! [B_83] :
      ( k2_lattices('#skF_5',B_83,k1_lattices('#skF_5',B_83,'#skF_7')) = B_83
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_642])).

tff(c_702,plain,(
    k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28,c_688])).

tff(c_722,plain,(
    k2_lattices('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_702])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_722])).

%------------------------------------------------------------------------------
