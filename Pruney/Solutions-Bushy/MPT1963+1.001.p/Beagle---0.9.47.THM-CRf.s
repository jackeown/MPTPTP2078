%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1963+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:43 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 249 expanded)
%              Number of leaves         :   40 ( 111 expanded)
%              Depth                    :   13
%              Number of atoms          :  235 ( 756 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_waybel_0 > v12_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_yellow_0 > v3_orders_2 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v1_orders_2 > v1_lattice3 > v11_waybel_1 > v10_waybel_1 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v11_waybel_1,type,(
    v11_waybel_1: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_yellow_0,type,(
    v3_yellow_0: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v10_waybel_1,type,(
    v10_waybel_1: $i > $o )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v12_waybel_0(B,k3_yellow_1(A))
          & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
       => ( v1_waybel_0(B,k3_yellow_1(A))
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B) )
             => r2_hidden(k2_xboole_0(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_7)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v11_waybel_1(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_waybel_7)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_yellow_0(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v1_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => r2_hidden(k13_lattice3(A,C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_waybel_0)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
            & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

tff(c_64,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_84,plain,(
    ~ v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_36,plain,(
    ! [A_4] : v5_orders_2(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_2] : l1_orders_2(k3_yellow_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_3] : v11_waybel_1(k3_yellow_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    ! [A_52] :
      ( v1_lattice3(A_52)
      | ~ v11_waybel_1(A_52)
      | v2_struct_0(A_52)
      | ~ l1_orders_2(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_4] : ~ v2_struct_0(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    ! [A_4] :
      ( v1_lattice3(k3_yellow_1(A_4))
      | ~ v11_waybel_1(k3_yellow_1(A_4))
      | ~ l1_orders_2(k3_yellow_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_87,c_28])).

tff(c_93,plain,(
    ! [A_4] : v1_lattice3(k3_yellow_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_90])).

tff(c_58,plain,(
    v12_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_157,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),B_82)
      | v1_waybel_0(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ v12_waybel_0(B_82,A_81)
      | ~ l1_orders_2(A_81)
      | ~ v1_lattice3(A_81)
      | ~ v5_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_159,plain,
    ( r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ v12_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ l1_orders_2(k3_yellow_1('#skF_3'))
    | ~ v1_lattice3(k3_yellow_1('#skF_3'))
    | ~ v5_orders_2(k3_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_157])).

tff(c_162,plain,
    ( r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93,c_22,c_58,c_159])).

tff(c_163,plain,(
    r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_162])).

tff(c_164,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_2'(A_83,B_84),B_84)
      | v1_waybel_0(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ v12_waybel_0(B_84,A_83)
      | ~ l1_orders_2(A_83)
      | ~ v1_lattice3(A_83)
      | ~ v5_orders_2(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_166,plain,
    ( r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ v12_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ l1_orders_2(k3_yellow_1('#skF_3'))
    | ~ v1_lattice3(k3_yellow_1('#skF_3'))
    | ~ v5_orders_2(k3_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_164])).

tff(c_169,plain,
    ( r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93,c_22,c_58,c_166])).

tff(c_170,plain,(
    r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_169])).

tff(c_74,plain,(
    ! [C_41,D_42] :
      ( v1_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | r2_hidden(k2_xboole_0(C_41,D_42),'#skF_4')
      | ~ r2_hidden(D_42,'#skF_4')
      | ~ r2_hidden(C_41,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_121,plain,(
    ! [C_41,D_42] :
      ( r2_hidden(k2_xboole_0(C_41,D_42),'#skF_4')
      | ~ r2_hidden(D_42,'#skF_4')
      | ~ r2_hidden(C_41,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_74])).

tff(c_171,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_1'(A_85,B_86),u1_struct_0(A_85))
      | v1_waybel_0(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v12_waybel_0(B_86,A_85)
      | ~ l1_orders_2(A_85)
      | ~ v1_lattice3(A_85)
      | ~ v5_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_114,plain,(
    ! [A_61,C_62,B_63] :
      ( m1_subset_1(A_61,C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_117,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_123,plain,(
    ! [A_67,B_68,C_69] :
      ( k13_lattice3(k3_yellow_1(A_67),B_68,C_69) = k2_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(k3_yellow_1(A_67)))
      | ~ m1_subset_1(B_68,u1_struct_0(k3_yellow_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_126,plain,(
    ! [B_68,A_61] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),B_68,A_61) = k2_xboole_0(B_68,A_61)
      | ~ m1_subset_1(B_68,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_117,c_123])).

tff(c_180,plain,(
    ! [B_86,A_61] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),B_86),A_61) = k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),B_86),A_61)
      | ~ r2_hidden(A_61,'#skF_4')
      | v1_waybel_0(B_86,k3_yellow_1('#skF_3'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3'))))
      | ~ v12_waybel_0(B_86,k3_yellow_1('#skF_3'))
      | ~ l1_orders_2(k3_yellow_1('#skF_3'))
      | ~ v1_lattice3(k3_yellow_1('#skF_3'))
      | ~ v5_orders_2(k3_yellow_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_171,c_126])).

tff(c_263,plain,(
    ! [B_98,A_99] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),B_98),A_99) = k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),B_98),A_99)
      | ~ r2_hidden(A_99,'#skF_4')
      | v1_waybel_0(B_98,k3_yellow_1('#skF_3'))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3'))))
      | ~ v12_waybel_0(B_98,k3_yellow_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93,c_22,c_180])).

tff(c_265,plain,(
    ! [A_99] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_99) = k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_99)
      | ~ r2_hidden(A_99,'#skF_4')
      | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | ~ v12_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_263])).

tff(c_268,plain,(
    ! [A_99] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_99) = k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_99)
      | ~ r2_hidden(A_99,'#skF_4')
      | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_265])).

tff(c_270,plain,(
    ! [A_100] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_100) = k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_100)
      | ~ r2_hidden(A_100,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_268])).

tff(c_44,plain,(
    ! [A_9,B_23] :
      ( ~ r2_hidden(k13_lattice3(A_9,'#skF_1'(A_9,B_23),'#skF_2'(A_9,B_23)),B_23)
      | v1_waybel_0(B_23,A_9)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ v12_waybel_0(B_23,A_9)
      | ~ l1_orders_2(A_9)
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_277,plain,
    ( ~ r2_hidden(k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_2'(k3_yellow_1('#skF_3'),'#skF_4')),'#skF_4')
    | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3'))))
    | ~ v12_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ l1_orders_2(k3_yellow_1('#skF_3'))
    | ~ v1_lattice3(k3_yellow_1('#skF_3'))
    | ~ v5_orders_2(k3_yellow_1('#skF_3'))
    | ~ r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_44])).

tff(c_290,plain,
    ( ~ r2_hidden(k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_2'(k3_yellow_1('#skF_3'),'#skF_4')),'#skF_4')
    | v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_36,c_93,c_22,c_58,c_56,c_277])).

tff(c_291,plain,(
    ~ r2_hidden(k2_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_2'(k3_yellow_1('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_290])).

tff(c_301,plain,
    ( ~ r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_291])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_170,c_301])).

tff(c_306,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_307,plain,(
    v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_309,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_62])).

tff(c_340,plain,(
    ! [A_111,C_112,B_113] :
      ( m1_subset_1(A_111,C_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(C_112))
      | ~ r2_hidden(A_111,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_343,plain,(
    ! [A_111] :
      ( m1_subset_1(A_111,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_111,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_340])).

tff(c_349,plain,(
    ! [A_116,B_117,C_118] :
      ( k13_lattice3(k3_yellow_1(A_116),B_117,C_118) = k2_xboole_0(B_117,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0(k3_yellow_1(A_116)))
      | ~ m1_subset_1(B_117,u1_struct_0(k3_yellow_1(A_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_353,plain,(
    ! [B_119,A_120] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),B_119,A_120) = k2_xboole_0(B_119,A_120)
      | ~ m1_subset_1(B_119,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_120,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_343,c_349])).

tff(c_356,plain,(
    ! [A_111,A_120] :
      ( k13_lattice3(k3_yellow_1('#skF_3'),A_111,A_120) = k2_xboole_0(A_111,A_120)
      | ~ r2_hidden(A_120,'#skF_4')
      | ~ r2_hidden(A_111,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_343,c_353])).

tff(c_333,plain,(
    ! [A_110] :
      ( v1_lattice3(A_110)
      | ~ v11_waybel_1(A_110)
      | v2_struct_0(A_110)
      | ~ l1_orders_2(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_336,plain,(
    ! [A_4] :
      ( v1_lattice3(k3_yellow_1(A_4))
      | ~ v11_waybel_1(k3_yellow_1(A_4))
      | ~ l1_orders_2(k3_yellow_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_333,c_28])).

tff(c_339,plain,(
    ! [A_4] : v1_lattice3(k3_yellow_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_336])).

tff(c_464,plain,(
    ! [A_144,C_145,D_146,B_147] :
      ( r2_hidden(k13_lattice3(A_144,C_145,D_146),B_147)
      | ~ r2_hidden(D_146,B_147)
      | ~ r2_hidden(C_145,B_147)
      | ~ m1_subset_1(D_146,u1_struct_0(A_144))
      | ~ m1_subset_1(C_145,u1_struct_0(A_144))
      | ~ v1_waybel_0(B_147,A_144)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v12_waybel_0(B_147,A_144)
      | ~ l1_orders_2(A_144)
      | ~ v1_lattice3(A_144)
      | ~ v5_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_466,plain,(
    ! [C_145,D_146] :
      ( r2_hidden(k13_lattice3(k3_yellow_1('#skF_3'),C_145,D_146),'#skF_4')
      | ~ r2_hidden(D_146,'#skF_4')
      | ~ r2_hidden(C_145,'#skF_4')
      | ~ m1_subset_1(D_146,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ m1_subset_1(C_145,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ v1_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | ~ v12_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | ~ l1_orders_2(k3_yellow_1('#skF_3'))
      | ~ v1_lattice3(k3_yellow_1('#skF_3'))
      | ~ v5_orders_2(k3_yellow_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_464])).

tff(c_470,plain,(
    ! [C_148,D_149] :
      ( r2_hidden(k13_lattice3(k3_yellow_1('#skF_3'),C_148,D_149),'#skF_4')
      | ~ r2_hidden(D_149,'#skF_4')
      | ~ r2_hidden(C_148,'#skF_4')
      | ~ m1_subset_1(D_149,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ m1_subset_1(C_148,u1_struct_0(k3_yellow_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_339,c_22,c_58,c_307,c_466])).

tff(c_481,plain,(
    ! [A_150,A_151] :
      ( r2_hidden(k2_xboole_0(A_150,A_151),'#skF_4')
      | ~ r2_hidden(A_151,'#skF_4')
      | ~ r2_hidden(A_150,'#skF_4')
      | ~ m1_subset_1(A_151,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ m1_subset_1(A_150,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_151,'#skF_4')
      | ~ r2_hidden(A_150,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_470])).

tff(c_497,plain,(
    ! [A_152,A_153] :
      ( r2_hidden(k2_xboole_0(A_152,A_153),'#skF_4')
      | ~ m1_subset_1(A_152,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_152,'#skF_4')
      | ~ r2_hidden(A_153,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_343,c_481])).

tff(c_513,plain,(
    ! [A_154,A_155] :
      ( r2_hidden(k2_xboole_0(A_154,A_155),'#skF_4')
      | ~ r2_hidden(A_155,'#skF_4')
      | ~ r2_hidden(A_154,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_343,c_497])).

tff(c_60,plain,
    ( ~ r2_hidden(k2_xboole_0('#skF_5','#skF_6'),'#skF_4')
    | ~ v1_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_322,plain,(
    ~ r2_hidden(k2_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_60])).

tff(c_516,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_513,c_322])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_309,c_516])).

%------------------------------------------------------------------------------
