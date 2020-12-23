%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:13 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 208 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 ( 841 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattices(A,B,C)
                     => r1_lattices(A,k2_lattices(A,B,D),k2_lattices(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

tff(f_90,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v7_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k2_lattices(A,B,k2_lattices(A,C,D)) = k2_lattices(A,k2_lattices(A,B,C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).

tff(f_109,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    ! [A_68] :
      ( l1_lattices(A_68)
      | ~ l3_lattices(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    l1_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_24,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1(k2_lattices(A_45,B_46,C_47),u1_struct_0(A_45))
      | ~ m1_subset_1(C_47,u1_struct_0(A_45))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    v7_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_815,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k2_lattices(A_103,k2_lattices(A_103,B_104,C_105),D_106) = k2_lattices(A_103,B_104,k2_lattices(A_103,C_105,D_106))
      | ~ m1_subset_1(D_106,u1_struct_0(A_103))
      | ~ m1_subset_1(C_105,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ v7_lattices(A_103)
      | ~ l1_lattices(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_831,plain,(
    ! [B_104,C_105] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_104,C_105),'#skF_8') = k2_lattices('#skF_6',B_104,k2_lattices('#skF_6',C_105,'#skF_8'))
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_6'))
      | ~ v7_lattices('#skF_6')
      | ~ l1_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_815])).

tff(c_846,plain,(
    ! [B_104,C_105] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_104,C_105),'#skF_8') = k2_lattices('#skF_6',B_104,k2_lattices('#skF_6',C_105,'#skF_8'))
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_831])).

tff(c_1009,plain,(
    ! [B_116,C_117] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_116,C_117),'#skF_8') = k2_lattices('#skF_6',B_116,k2_lattices('#skF_6',C_117,'#skF_8'))
      | ~ m1_subset_1(C_117,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_116,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_846])).

tff(c_3430,plain,(
    ! [B_144] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_144,'#skF_9'),'#skF_8') = k2_lattices('#skF_6',B_144,k2_lattices('#skF_6','#skF_9','#skF_8'))
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1009])).

tff(c_3534,plain,(
    k2_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),'#skF_8') = k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_42,c_3430])).

tff(c_3552,plain,
    ( m1_subset_1(k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6','#skF_9','#skF_8')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6'))
    | ~ l1_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3534,c_24])).

tff(c_3564,plain,
    ( m1_subset_1(k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6','#skF_9','#skF_8')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40,c_3552])).

tff(c_3565,plain,
    ( m1_subset_1(k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6','#skF_9','#skF_8')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3564])).

tff(c_4557,plain,(
    ~ m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3565])).

tff(c_4561,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_4557])).

tff(c_4564,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42,c_38,c_4561])).

tff(c_4566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4564])).

tff(c_4568,plain,(
    m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3565])).

tff(c_48,plain,(
    v8_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    v9_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    r1_lattices('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_421,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_lattices(A_91,B_92,C_93) = B_92
      | ~ r1_lattices(A_91,B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_91))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l3_lattices(A_91)
      | ~ v9_lattices(A_91)
      | ~ v8_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_423,plain,
    ( k2_lattices('#skF_6','#skF_7','#skF_8') = '#skF_7'
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_421])).

tff(c_426,plain,
    ( k2_lattices('#skF_6','#skF_7','#skF_8') = '#skF_7'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_423])).

tff(c_427,plain,(
    k2_lattices('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_426])).

tff(c_833,plain,(
    ! [B_104,C_105] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_104,C_105),'#skF_9') = k2_lattices('#skF_6',B_104,k2_lattices('#skF_6',C_105,'#skF_9'))
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_6'))
      | ~ v7_lattices('#skF_6')
      | ~ l1_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_815])).

tff(c_850,plain,(
    ! [B_104,C_105] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_104,C_105),'#skF_9') = k2_lattices('#skF_6',B_104,k2_lattices('#skF_6',C_105,'#skF_9'))
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_833])).

tff(c_896,plain,(
    ! [B_113,C_114] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_113,C_114),'#skF_9') = k2_lattices('#skF_6',B_113,k2_lattices('#skF_6',C_114,'#skF_9'))
      | ~ m1_subset_1(C_114,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_850])).

tff(c_6486,plain,(
    ! [B_168] :
      ( k2_lattices('#skF_6',k2_lattices('#skF_6',B_168,'#skF_8'),'#skF_9') = k2_lattices('#skF_6',B_168,k2_lattices('#skF_6','#skF_8','#skF_9'))
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_40,c_896])).

tff(c_6561,plain,(
    k2_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_8'),'#skF_9') = k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_42,c_6486])).

tff(c_6617,plain,(
    k2_lattices('#skF_6','#skF_7',k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_6561])).

tff(c_245,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_lattices(A_86,k2_lattices(A_86,B_87,C_88),C_88) = C_88
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ v8_lattices(A_86)
      | ~ l3_lattices(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_264,plain,(
    ! [A_45,B_87,B_46,C_47] :
      ( k1_lattices(A_45,k2_lattices(A_45,B_87,k2_lattices(A_45,B_46,C_47)),k2_lattices(A_45,B_46,C_47)) = k2_lattices(A_45,B_46,C_47)
      | ~ m1_subset_1(B_87,u1_struct_0(A_45))
      | ~ v8_lattices(A_45)
      | ~ l3_lattices(A_45)
      | ~ m1_subset_1(C_47,u1_struct_0(A_45))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_24,c_245])).

tff(c_6632,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v8_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6617,c_264])).

tff(c_6672,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_8','#skF_9')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40,c_38,c_44,c_48,c_42,c_6632])).

tff(c_6673,plain,(
    k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),k2_lattices('#skF_6','#skF_8','#skF_9')) = k2_lattices('#skF_6','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6672])).

tff(c_53,plain,(
    ! [A_67] :
      ( l2_lattices(A_67)
      | ~ l3_lattices(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_57,plain,(
    l2_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_70,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_lattices(A_78,B_79,C_80)
      | k1_lattices(A_78,B_79,C_80) != C_80
      | ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l2_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4374,plain,(
    ! [A_151,B_152,B_153,C_154] :
      ( r1_lattices(A_151,B_152,k2_lattices(A_151,B_153,C_154))
      | k1_lattices(A_151,B_152,k2_lattices(A_151,B_153,C_154)) != k2_lattices(A_151,B_153,C_154)
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l2_lattices(A_151)
      | ~ m1_subset_1(C_154,u1_struct_0(A_151))
      | ~ m1_subset_1(B_153,u1_struct_0(A_151))
      | ~ l1_lattices(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_34,plain,(
    ~ r1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),k2_lattices('#skF_6','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4381,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),k2_lattices('#skF_6','#skF_8','#skF_9')) != k2_lattices('#skF_6','#skF_8','#skF_9')
    | ~ m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6'))
    | ~ l2_lattices('#skF_6')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4374,c_34])).

tff(c_4473,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),k2_lattices('#skF_6','#skF_8','#skF_9')) != k2_lattices('#skF_6','#skF_8','#skF_9')
    | ~ m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40,c_38,c_57,c_4381])).

tff(c_4474,plain,
    ( k1_lattices('#skF_6',k2_lattices('#skF_6','#skF_7','#skF_9'),k2_lattices('#skF_6','#skF_8','#skF_9')) != k2_lattices('#skF_6','#skF_8','#skF_9')
    | ~ m1_subset_1(k2_lattices('#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4473])).

tff(c_8869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4568,c_6673,c_4474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.63/3.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/3.08  
% 7.63/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/3.08  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 7.63/3.08  
% 7.63/3.08  %Foreground sorts:
% 7.63/3.08  
% 7.63/3.08  
% 7.63/3.08  %Background operators:
% 7.63/3.08  
% 7.63/3.08  
% 7.63/3.08  %Foreground operators:
% 7.63/3.08  tff(l3_lattices, type, l3_lattices: $i > $o).
% 7.63/3.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.63/3.08  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 7.63/3.08  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.63/3.08  tff(l2_lattices, type, l2_lattices: $i > $o).
% 7.63/3.08  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.63/3.08  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.63/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.63/3.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.63/3.08  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 7.63/3.08  tff(l1_lattices, type, l1_lattices: $i > $o).
% 7.63/3.08  tff('#skF_7', type, '#skF_7': $i).
% 7.63/3.08  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 7.63/3.08  tff('#skF_6', type, '#skF_6': $i).
% 7.63/3.08  tff(v9_lattices, type, v9_lattices: $i > $o).
% 7.63/3.08  tff('#skF_9', type, '#skF_9': $i).
% 7.63/3.08  tff('#skF_8', type, '#skF_8': $i).
% 7.63/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.63/3.08  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.63/3.08  tff(v8_lattices, type, v8_lattices: $i > $o).
% 7.63/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.63/3.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.63/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.63/3.08  tff(v7_lattices, type, v7_lattices: $i > $o).
% 7.63/3.08  
% 7.87/3.10  tff(f_134, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattices(A, B, C) => r1_lattices(A, k2_lattices(A, B, D), k2_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_lattices)).
% 7.87/3.10  tff(f_90, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 7.87/3.10  tff(f_84, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k2_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 7.87/3.10  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v7_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k2_lattices(A, B, k2_lattices(A, C, D)) = k2_lattices(A, k2_lattices(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_lattices)).
% 7.87/3.10  tff(f_109, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 7.87/3.10  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 7.87/3.10  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 7.87/3.10  tff(c_52, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_44, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_58, plain, (![A_68]: (l1_lattices(A_68) | ~l3_lattices(A_68))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.87/3.10  tff(c_62, plain, (l1_lattices('#skF_6')), inference(resolution, [status(thm)], [c_44, c_58])).
% 7.87/3.10  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_38, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_24, plain, (![A_45, B_46, C_47]: (m1_subset_1(k2_lattices(A_45, B_46, C_47), u1_struct_0(A_45)) | ~m1_subset_1(C_47, u1_struct_0(A_45)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.87/3.10  tff(c_40, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_50, plain, (v7_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_815, plain, (![A_103, B_104, C_105, D_106]: (k2_lattices(A_103, k2_lattices(A_103, B_104, C_105), D_106)=k2_lattices(A_103, B_104, k2_lattices(A_103, C_105, D_106)) | ~m1_subset_1(D_106, u1_struct_0(A_103)) | ~m1_subset_1(C_105, u1_struct_0(A_103)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~v7_lattices(A_103) | ~l1_lattices(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.87/3.10  tff(c_831, plain, (![B_104, C_105]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_104, C_105), '#skF_8')=k2_lattices('#skF_6', B_104, k2_lattices('#skF_6', C_105, '#skF_8')) | ~m1_subset_1(C_105, u1_struct_0('#skF_6')) | ~m1_subset_1(B_104, u1_struct_0('#skF_6')) | ~v7_lattices('#skF_6') | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_815])).
% 7.87/3.10  tff(c_846, plain, (![B_104, C_105]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_104, C_105), '#skF_8')=k2_lattices('#skF_6', B_104, k2_lattices('#skF_6', C_105, '#skF_8')) | ~m1_subset_1(C_105, u1_struct_0('#skF_6')) | ~m1_subset_1(B_104, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_831])).
% 7.87/3.10  tff(c_1009, plain, (![B_116, C_117]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_116, C_117), '#skF_8')=k2_lattices('#skF_6', B_116, k2_lattices('#skF_6', C_117, '#skF_8')) | ~m1_subset_1(C_117, u1_struct_0('#skF_6')) | ~m1_subset_1(B_116, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_52, c_846])).
% 7.87/3.10  tff(c_3430, plain, (![B_144]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_144, '#skF_9'), '#skF_8')=k2_lattices('#skF_6', B_144, k2_lattices('#skF_6', '#skF_9', '#skF_8')) | ~m1_subset_1(B_144, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_38, c_1009])).
% 7.87/3.10  tff(c_3534, plain, (k2_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), '#skF_8')=k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_42, c_3430])).
% 7.87/3.10  tff(c_3552, plain, (m1_subset_1(k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', '#skF_9', '#skF_8')), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3534, c_24])).
% 7.87/3.10  tff(c_3564, plain, (m1_subset_1(k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', '#skF_9', '#skF_8')), u1_struct_0('#skF_6')) | ~m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40, c_3552])).
% 7.87/3.10  tff(c_3565, plain, (m1_subset_1(k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', '#skF_9', '#skF_8')), u1_struct_0('#skF_6')) | ~m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_3564])).
% 7.87/3.10  tff(c_4557, plain, (~m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_3565])).
% 7.87/3.10  tff(c_4561, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_24, c_4557])).
% 7.87/3.10  tff(c_4564, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42, c_38, c_4561])).
% 7.87/3.10  tff(c_4566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_4564])).
% 7.87/3.10  tff(c_4568, plain, (m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_3565])).
% 7.87/3.10  tff(c_48, plain, (v8_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_46, plain, (v9_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_36, plain, (r1_lattices('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_421, plain, (![A_91, B_92, C_93]: (k2_lattices(A_91, B_92, C_93)=B_92 | ~r1_lattices(A_91, B_92, C_93) | ~m1_subset_1(C_93, u1_struct_0(A_91)) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l3_lattices(A_91) | ~v9_lattices(A_91) | ~v8_lattices(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.87/3.10  tff(c_423, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_8')='#skF_7' | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_421])).
% 7.87/3.10  tff(c_426, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_8')='#skF_7' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_423])).
% 7.87/3.10  tff(c_427, plain, (k2_lattices('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_52, c_426])).
% 7.87/3.10  tff(c_833, plain, (![B_104, C_105]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_104, C_105), '#skF_9')=k2_lattices('#skF_6', B_104, k2_lattices('#skF_6', C_105, '#skF_9')) | ~m1_subset_1(C_105, u1_struct_0('#skF_6')) | ~m1_subset_1(B_104, u1_struct_0('#skF_6')) | ~v7_lattices('#skF_6') | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_815])).
% 7.87/3.10  tff(c_850, plain, (![B_104, C_105]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_104, C_105), '#skF_9')=k2_lattices('#skF_6', B_104, k2_lattices('#skF_6', C_105, '#skF_9')) | ~m1_subset_1(C_105, u1_struct_0('#skF_6')) | ~m1_subset_1(B_104, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_833])).
% 7.87/3.10  tff(c_896, plain, (![B_113, C_114]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_113, C_114), '#skF_9')=k2_lattices('#skF_6', B_113, k2_lattices('#skF_6', C_114, '#skF_9')) | ~m1_subset_1(C_114, u1_struct_0('#skF_6')) | ~m1_subset_1(B_113, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_52, c_850])).
% 7.87/3.10  tff(c_6486, plain, (![B_168]: (k2_lattices('#skF_6', k2_lattices('#skF_6', B_168, '#skF_8'), '#skF_9')=k2_lattices('#skF_6', B_168, k2_lattices('#skF_6', '#skF_8', '#skF_9')) | ~m1_subset_1(B_168, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_40, c_896])).
% 7.87/3.10  tff(c_6561, plain, (k2_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_8'), '#skF_9')=k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_42, c_6486])).
% 7.87/3.10  tff(c_6617, plain, (k2_lattices('#skF_6', '#skF_7', k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_6561])).
% 7.87/3.10  tff(c_245, plain, (![A_86, B_87, C_88]: (k1_lattices(A_86, k2_lattices(A_86, B_87, C_88), C_88)=C_88 | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~v8_lattices(A_86) | ~l3_lattices(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.87/3.10  tff(c_264, plain, (![A_45, B_87, B_46, C_47]: (k1_lattices(A_45, k2_lattices(A_45, B_87, k2_lattices(A_45, B_46, C_47)), k2_lattices(A_45, B_46, C_47))=k2_lattices(A_45, B_46, C_47) | ~m1_subset_1(B_87, u1_struct_0(A_45)) | ~v8_lattices(A_45) | ~l3_lattices(A_45) | ~m1_subset_1(C_47, u1_struct_0(A_45)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_lattices(A_45) | v2_struct_0(A_45))), inference(resolution, [status(thm)], [c_24, c_245])).
% 7.87/3.10  tff(c_6632, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v8_lattices('#skF_6') | ~l3_lattices('#skF_6') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6617, c_264])).
% 7.87/3.10  tff(c_6672, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_8', '#skF_9') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40, c_38, c_44, c_48, c_42, c_6632])).
% 7.87/3.10  tff(c_6673, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))=k2_lattices('#skF_6', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_52, c_6672])).
% 7.87/3.10  tff(c_53, plain, (![A_67]: (l2_lattices(A_67) | ~l3_lattices(A_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.87/3.10  tff(c_57, plain, (l2_lattices('#skF_6')), inference(resolution, [status(thm)], [c_44, c_53])).
% 7.87/3.10  tff(c_70, plain, (![A_78, B_79, C_80]: (r1_lattices(A_78, B_79, C_80) | k1_lattices(A_78, B_79, C_80)!=C_80 | ~m1_subset_1(C_80, u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l2_lattices(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.87/3.10  tff(c_4374, plain, (![A_151, B_152, B_153, C_154]: (r1_lattices(A_151, B_152, k2_lattices(A_151, B_153, C_154)) | k1_lattices(A_151, B_152, k2_lattices(A_151, B_153, C_154))!=k2_lattices(A_151, B_153, C_154) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l2_lattices(A_151) | ~m1_subset_1(C_154, u1_struct_0(A_151)) | ~m1_subset_1(B_153, u1_struct_0(A_151)) | ~l1_lattices(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_24, c_70])).
% 7.87/3.10  tff(c_34, plain, (~r1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.87/3.10  tff(c_4381, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))!=k2_lattices('#skF_6', '#skF_8', '#skF_9') | ~m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6')) | ~l2_lattices('#skF_6') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4374, c_34])).
% 7.87/3.10  tff(c_4473, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))!=k2_lattices('#skF_6', '#skF_8', '#skF_9') | ~m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40, c_38, c_57, c_4381])).
% 7.87/3.10  tff(c_4474, plain, (k1_lattices('#skF_6', k2_lattices('#skF_6', '#skF_7', '#skF_9'), k2_lattices('#skF_6', '#skF_8', '#skF_9'))!=k2_lattices('#skF_6', '#skF_8', '#skF_9') | ~m1_subset_1(k2_lattices('#skF_6', '#skF_7', '#skF_9'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_4473])).
% 7.87/3.10  tff(c_8869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4568, c_6673, c_4474])).
% 7.87/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/3.10  
% 7.87/3.10  Inference rules
% 7.87/3.10  ----------------------
% 7.87/3.10  #Ref     : 0
% 7.87/3.10  #Sup     : 1772
% 7.87/3.10  #Fact    : 0
% 7.87/3.10  #Define  : 0
% 7.87/3.10  #Split   : 36
% 7.87/3.10  #Chain   : 0
% 7.87/3.10  #Close   : 0
% 7.87/3.10  
% 7.87/3.10  Ordering : KBO
% 7.87/3.10  
% 7.87/3.10  Simplification rules
% 7.87/3.10  ----------------------
% 7.87/3.10  #Subsume      : 13
% 7.87/3.10  #Demod        : 4033
% 7.87/3.10  #Tautology    : 770
% 7.87/3.10  #SimpNegUnit  : 718
% 7.87/3.10  #BackRed      : 16
% 7.87/3.10  
% 7.87/3.10  #Partial instantiations: 0
% 7.87/3.10  #Strategies tried      : 1
% 7.87/3.10  
% 7.87/3.10  Timing (in seconds)
% 7.87/3.10  ----------------------
% 7.87/3.10  Preprocessing        : 0.31
% 7.87/3.10  Parsing              : 0.17
% 7.87/3.10  CNF conversion       : 0.03
% 7.87/3.10  Main loop            : 1.92
% 7.87/3.10  Inferencing          : 0.50
% 7.87/3.10  Reduction            : 0.88
% 7.87/3.10  Demodulation         : 0.68
% 7.87/3.10  BG Simplification    : 0.06
% 7.87/3.10  Subsumption          : 0.38
% 7.87/3.10  Abstraction          : 0.10
% 7.87/3.10  MUC search           : 0.00
% 7.87/3.10  Cooper               : 0.00
% 7.87/3.10  Total                : 2.27
% 7.87/3.10  Index Insertion      : 0.00
% 7.87/3.10  Index Deletion       : 0.00
% 7.87/3.10  Index Matching       : 0.00
% 7.87/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
